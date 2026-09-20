"""IT5005 Sudoku — 组员 A：知识库建模交付文件

用途
----
这是独立交接文件，包含 A 的完整代码和概念题 1、4 的中文材料。
后续将本文件的定义合入最终 sudoku_solver.py，再加入自己的推理函数。
最终 sudoku_solver.py 仍只从 utils.py 和 logic_.py 导入；应合并这些定义，
不要在最终求解器中增加对 sudoku_solver_A 的导入。

运行依赖
--------
把本文件与老师提供的 utils.py、logic_.py 放在同一目录。
正常运行需要安装 numpy 和 networkx。两个老师文件以及 atom() 均保持原样。
本文件不读取 puzzles.json 或标准答案；调用方负责传入 givens。

已完成
--------
1. atom：原样保留老师的符号创建函数。
2. _check_input：输入格式、尺寸、取值范围及 givens 局部冲突检查。
3. _peers：同行、同列、同宫的去重同伴格集合。
4. build_general_kb：一般 CNF 数独知识库。
5. _IndexedDefiniteKB：确定子句知识库及前提/结论索引。
6. build_definite_kb：已知事实、格内排除、同伴排除、最后候选规则。
7. 文件末尾 CONCEPT_Q1_ZH、CONCEPT_Q4_ZH：交给 D 汇总到 Notebook 的答案材料。

与求解的接口约定
---------------
输入：n, box_h, box_w, givens，其中 givens = {(r, c): v}，全部从 1 开始。
build_general_kb(...) 返回 PropKB。
build_definite_kb(...) 返回 _IndexedDefiniteKB，它是 PropDefiniteKB 的子类。

确定子句知识库提供：
  clauses      : 全部事实和规则，规则格式为 Expr('==>', 前提, 结论)。
  facts        : 初始事实集合 set[Expr]。
  by_head      : {结论: [前提元组, ...]}；单独的事实保存在 facts。
  by_premise   : {前提: [完整规则表达式, ...]}。
  fc_seen      : set[Expr]；clauses_with_premise(p) 会先记录已处理原子 p。
  version      : 知识库修改标记，供 B 判断缓存有效性。
  _bc_state    : 初始为 None，由 B 的后向算法建立和使用。

通过 tell/retract 修改知识库，以维护索引并清除缓存；不要直接改 clauses。
已知 Is 与排除 Not 都是正命题原子；Not 不是自动绑定的逻辑否定 ~Is。

接下来实现：solve_full_grid_fc、pl_bc_entails、solve_full_grid_bc，
以及其需要的 _backward_state、get_proof_steps、_check_grid、UnsolvedPuzzleError。
这份文件只建立知识库；完整求解、推理轨迹和停滞处理后续。

交接检查示例（在导入本文件后执行）
----------------------------------
  kb = build_definite_kb(9, 3, 3, {(1, 2): 3})
  assert isinstance(kb, PropDefiniteKB)
  assert atom('Is', 1, 2, 3) in kb.facts
  assert pl_fc_entails(kb, atom('Not', 2, 2, 3))  # 同列排除
  assert pl_fc_entails(kb, atom('Not', 1, 2, 4))  # 格内排除

这个小例子只用于检查规则连接；一个已知数不要求能够解出整盘。
"""

from utils import *
from logic_ import *


# Do not change this function; it is used to create atomic propositions.
def atom(prefix, r, c, v):
    """prefix is 'Is' or 'Not'. Returns the Expr for e.g. Is3_2_4."""
    return expr(f'{prefix}{r}_{c}_{v}')


def _check_input(n, box_h, box_w, givens):
    if any(type(x) is not int or x < 1 for x in (n, box_h, box_w)):
        raise ValueError('Grid and box dimensions must be positive integers.')
    if box_h * box_w != n or n % box_h or n % box_w:
        raise ValueError('The boxes must tile the board and contain n cells.')
    rows, cols, boxes = set(), set(), set()
    for cell, value in givens.items():
        if not isinstance(cell, tuple) or len(cell) != 2:
            raise ValueError('Use (row, column) tuple keys, numbered from 1.')
        r, c = cell
        if any(type(x) is not int or not 1 <= x <= n for x in (r, c, value)):
            raise ValueError('Rows, columns and values must be integers in 1..n.')
        row, col = (r, value), (c, value)
        box = ((r - 1) // box_h, (c - 1) // box_w, value)
        if row in rows or col in cols or box in boxes:
            raise ValueError('Conflicting givens in a row, column or box.')
        rows.add(row)
        cols.add(col)
        boxes.add(box)


def _peers(n, box_h, box_w, r, c):
    """Distinct cells sharing a row, column or box, in a stable order."""
    return [(rr, cc) for rr in range(1, n + 1) for cc in range(1, n + 1)
            if (rr, cc) != (r, c) and
            (rr == r or cc == c or
             ((rr - 1) // box_h == (r - 1) // box_h and
              (cc - 1) // box_w == (c - 1) // box_w))]


def build_general_kb(n, box_h, box_w, givens):
    """Return a PropKB with all six Sudoku constraints as CNF clauses.

    Only Is atoms are needed here: logical negation is available directly.
    Peer-pair clauses are shared when a pair belongs to both a line and a box.
    """
    _check_input(n, box_h, box_w, givens)
    kb = PropKB()
    values = range(1, n + 1)
    symbols = {(r, c, v): atom('Is', r, c, v)
               for r in values for c in values for v in values}
    for r in values:
        for c in values:
            kb.tell(associate('|', [symbols[r, c, v] for v in values]))
            for v, w in combinations(values, 2):
                kb.tell(~symbols[r, c, v] | ~symbols[r, c, w])
            for rr, cc in _peers(n, box_h, box_w, r, c):
                if (r, c) < (rr, cc):
                    for v in values:
                        kb.tell(~symbols[r, c, v] | ~symbols[rr, cc, v])
    for (r, c), v in sorted(givens.items()):
        kb.tell(symbols[r, c, v])
    return kb


class _IndexedDefiniteKB(PropDefiniteKB):
    """The supplied KB with premise/head indexes; no inference is replaced.

    The library explicitly permits caching clauses_with_premise.  Recording
    atoms processed by that method lets the unchanged library FC routine
    expose its complete closure in one pass, instead of repeating it 729 times.
    Use tell/retract to mutate this KB so indexes and proof caches stay valid.
    """

    def __init__(self):
        super().__init__()
        self.by_premise = {}
        self.by_head = {}
        self.facts = set()
        self.version = 0
        self.fc_seen = set()
        self._bc_state = None

    def tell(self, sentence):
        super().tell(sentence)
        premises, head = parse_definite_clause(sentence)
        if not premises:
            self.facts.add(head)
        else:
            self.by_head.setdefault(head, []).append(tuple(dict.fromkeys(premises)))
            for premise in dict.fromkeys(premises):
                self.by_premise.setdefault(premise, []).append(sentence)
        self.version += 1
        self._bc_state = None
        self.fc_seen.clear()

    def retract(self, sentence):
        remaining = list(self.clauses)
        remaining.remove(sentence)
        self.__init__()
        for clause in remaining:
            self.tell(clause)

    def clauses_with_premise(self, p):
        self.fc_seen.add(p)
        return self.by_premise.get(p, ())


def build_definite_kb(n, box_h, box_w, givens):
    """Return a PropDefiniteKB for elimination and cell last-candidate rules.

    Not is a *positive atom*, not the operator ~.  This Horn theory derives
    sound consequences of Sudoku; it is not logically equivalent to full CNF
    Sudoku and need not solve a puzzle requiring more advanced techniques.
    """
    _check_input(n, box_h, box_w, givens)
    kb = _IndexedDefiniteKB()
    values = range(1, n + 1)
    yes = {(r, c, v): atom('Is', r, c, v)
           for r in values for c in values for v in values}
    no = {(r, c, v): atom('Not', r, c, v)
          for r in values for c in values for v in values}
    for (r, c), v in sorted(givens.items()):
        kb.tell(yes[r, c, v])
    for r in values:
        for c in values:
            peers = _peers(n, box_h, box_w, r, c)
            for v in values:
                for w in values:
                    if w != v:
                        kb.tell(Expr('==>', yes[r, c, v], no[r, c, w]))
                for rr, cc in peers:
                    kb.tell(Expr('==>', yes[r, c, v], no[rr, cc, v]))
                premises = [no[r, c, w] for w in values if w != v]
                if premises:
                    kb.tell(Expr('==>', associate('&', premises), yes[r, c, v]))
                else:  # The only value on a 1 x 1 board is 1.
                    kb.tell(yes[r, c, v])
    return kb

# 下列文字供 D 复制到 Notebook 对应概念题；不会参与知识库推理。
CONCEPT_Q1_ZH = r"""
概念题 1：一般表示与确定子句表示

记 I[r,c,v] 为格子 (r,c) 的值是 v，N[r,c,v] 为该格不能取 v。

(a) 一般 CNF 知识库
1. 每格至少一个值：I[r,c,1] OR ... OR I[r,c,n]。
2. 每格至多一个值：对 v < w，加入 ~I[r,c,v] OR ~I[r,c,w]。
3. 同行、同列、同宫不重复：对不同的同伴格 a,b 和每个值 v，
   加入 ~I[a,v] OR ~I[b,v]。
4. 对每个 given (r,c)=v，加入事实 I[r,c,v]。

行、列、宫统一通过 _peers 表达。它返回去重后的同伴格；建一般 KB 时，
仅对 (r,c) < (rr,cc) 的格子对加入约束，避免对称重复。
所有传给 PropKB.tell 的公式已经是 CNF 子句。
无需另加“每行每个数字至少一次”：每行有 n 格，每格恰取一个 1..n 的值，
又禁止重复，所以一行的 n 个不同值必然覆盖全部数字；列和宫同理。

标准 9x9 每格有 20 个同伴。第一题 30 个 givens 对应：
81 条至少一个值 + 81*C(9,2)=2916 条格内互斥
+ (81*20/2)*9=7290 条同伴互斥 + 30 条事实 = 10317 条子句。
一般 KB 只需要 729 个 Is 原子，直接用逻辑运算符 ~ 表示否定。

(b) 确定子句知识库
确定子句恰有一个正文字；一般 Horn 子句允许至多一个正文字。
PropDefiniteKB 接受单独的正事实，或“正原子的合取 ==> 一个正原子”。
因此不能直接加入含 n 个正文字的“至少一个值”析取。

本实现增加独立的正原子 Not，并编码数独的可靠排除规则：
- 已知事实：I[r,c,v]。
- 格内排除：I[r,c,v] ==> N[r,c,w]，w != v。
- 同伴排除：I[a,v] ==> N[b,v]，a、b 同行/同列/同宫。
- 最后候选：AND(N[r,c,w] for w != v) ==> I[r,c,v]。

例如 I[1,2,3] 推出 N[2,2,3]；某格另外八个数都被明确证明排除后，
才能推出唯一剩余的数。不能用“尚未证明 Is”为理由直接推出 Not。
1x1 棋盘的最后候选规则没有前提，直接加入唯一的 Is1_1_1 事实。

第一题的 Horn KB 包含：
81*9*8=5832 条格内排除 + 81*9*20=14580 条同伴排除
+ 81*9=729 条最后候选 + 30 条 givens = 21171 条规则/事实。
它使用 Is、Not 两族共 1458 个不同的命题原子。

表达能力边界：Not 是正原子的名字，不自动等于 ~Is。
最后候选规则是从数独约束得到的可靠推理规则，并不是原正析取的等价改写。
把所有 Is、Not 原子都赋真，也会满足这套纯确定子句，所以它不能完整强制
数独的互斥语义。这是对有效数独可靠的推理规则集合，而不是完整 CNF 的
逻辑等价转换；对 Horn KB 推理完备，不等于可以解出所有数独。
给定题库可由这些基础规则解决；超出能力时，B 的求解器应报告未解格。

索引说明：_IndexedDefiniteKB 继承老师的 PropDefiniteKB，没有修改支持文件。
by_premise 供 FC 快速找到受影响的规则，by_head 供 BC 找到目标的候选规则。
clauses_with_premise 在原 FC 算法处理一个原子时记录到 fc_seen，方便 B 在
一次完整闭包计算后读取所有结论。增删知识时清空推理状态，避免旧缓存失效。
输入验证检查局部冲突，不预先证明题目唯一可解。
"""


CONCEPT_Q4_ZH = r"""
概念题 4：用相同 Is/Not 词汇编码 Naked Pairs（裸对）

设 U 为一行、一列或一个宫；a、b 是其中两个不同格子；x、y 是两个不同值。
设前提 P 为：
  AND(N[a,v] for v not in {x,y})
  AND
  AND(N[b,v] for v not in {x,y})。
即已有正面证据表明，两个格子的值都只能来自 {x,y}。

对每个其他格子 u in U - {a,b}，分别加入两条规则：
  P ==> N[u,x]
  P ==> N[u,y]

每条规则的前提都是正原子 Not，结论只有一个正原子，所以符合确定子句格式。
两个结论必须分别写成两条规则。本编码不需要“某排除事实尚未被证明”这样的
否定式条件，也没有把缺少证明当作候选存在的依据。

可靠性理由：在有效数独中，a、b 各有一个值，同一单元内不能重复。
既然它们都只能从 {x,y} 取值，就必然合起来占据 x 和 y，其他格子不能再取
这两个值。即使其中一格已确定，这个排除结论仍然成立。

例子：某行两个格子都已经排除除 2 和 7 外的所有数字，那么该行其余七格
可以排除 2 和 7；新增的排除事实可能继续触发最后候选规则。

代价：9x9 数独有 27 个单元，每个单元有 C(9,2)=36 对格子、36 对数字，
每个配置对另外 7 个格子各写两条规则。朴素枚举约增加：
  27 * 36 * 36 * 7 * 2 = 489888 条规则（未去重）。
每条规则有 2*(9-2)=14 个前提，会增加建库、索引、存储及推理成本。
高级规则能扩大可解题目范围，但并不保证解出所有数独。

本文件按作业基础要求实现排除和最后候选。上述裸对是概念题的编码方案，
没有把近 49 万条扩展规则加入 build_definite_kb。


"""

""" AI 的 Sudoku Solver 参考，实际编写自己完成就好
    class UnsolvedPuzzleError(ValueError):
       
    
        def __init__(self, partial_grid, n):
            self.partial_grid = dict(partial_grid)
            super().__init__(f'Horn inference filled {len(partial_grid)}/{n * n} cells. '
                             'The remaining cells need stronger rules or search.')
    
    
    def _check_grid(grid, n, box_h, box_w, givens):
        if len(grid) != n * n:
            raise UnsolvedPuzzleError(grid, n)
        _check_input(n, box_h, box_w, grid)
        if any(grid[cell] != value for cell, value in givens.items()):
            raise ValueError('An inferred grid contradicts a given.')
        return grid
    
    
    def solve_full_grid_fc(n, box_h, box_w, givens):
      
        kb = build_definite_kb(n, box_h, box_w, givens)
        pl_fc_entails(kb, Expr('SudokuClosureSentinel'))
        grid = {}
        for r in range(1, n + 1):
            for c in range(1, n + 1):
                entailed = [v for v in range(1, n + 1)
                            if atom('Is', r, c, v) in kb.fc_seen]
                if len(entailed) > 1:
                    raise ValueError('The KB derives conflicting values for a cell.')
                if entailed:
                    grid[r, c] = entailed[0]
        return _check_grid(grid, n, box_h, box_w, givens)
    
    
    def _backward_state(kb):
     
        marker = kb.version if isinstance(kb, _IndexedDefiniteKB) else tuple(kb.clauses)
        state = getattr(kb, '_bc_state', None)
        if state is not None and state['marker'] == marker:
            return state
        if isinstance(kb, _IndexedDefiniteKB):
            facts, by_head = set(kb.facts), kb.by_head
        else:
            facts, by_head = set(), {}
            for clause in kb.clauses:
                premises, head = parse_definite_clause(clause)
                if premises:
                    by_head.setdefault(head, []).append(tuple(dict.fromkeys(premises)))
                else:
                    facts.add(head)
        state = {'marker': marker, 'by_head': by_head, 'known': facts,
                 'expanded': set(), 'waiting': {}, 'pending': [],
                 'rules': [], 'proofs': {p: () for p in facts}}
        kb._bc_state = state
        return state
    
    
    def pl_bc_entails(kb, query):
     
        query = expr(query) if isinstance(query, str) else query
        if not isinstance(query, Expr) or query.args or not is_prop_symbol(query.op):
            raise ValueError('Backward chaining queries must be propositional atoms.')
        state = _backward_state(kb)
        known = state['known']
        if query in known:
            return True
        goals, newly_proved = [query], []
    
        def establish(head, premises):
            if head not in known:
                known.add(head)
                state['proofs'][head] = premises
                newly_proved.append(head)
    
        while goals or newly_proved:
            # Resume suspended AND rules whenever a needed subgoal is proved.
            if newly_proved:
                proved = newly_proved.pop()
                for rule_id in state['waiting'].pop(proved, ()):
                    missing = state['pending'][rule_id]
                    missing.discard(proved)
                    if not missing:
                        head, premises = state['rules'][rule_id]
                        establish(head, premises)
                continue
    
            goal = goals.pop()
            if goal in known or goal in state['expanded']:
                continue
            state['expanded'].add(goal)
            # Register every alternative before descending into the subgoals.
            # This keeps a recursive cycle alive if another branch later proves it.
            subgoals = []
            for premises in state['by_head'].get(goal, ()):
                missing = {p for p in premises if p not in known}
                if not missing:
                    establish(goal, premises)
                else:
                    rule_id = len(state['rules'])
                    state['rules'].append((goal, premises))
                    state['pending'].append(missing)
                    for premise in premises:
                        if premise in missing:
                            state['waiting'].setdefault(premise, []).append(rule_id)
                            subgoals.append(premise)
            # Reverse preserves the premise order of a conventional recursive DFS.
            goals.extend(reversed(subgoals))
        return query in known
    
    
    def get_proof_steps(kb, query):
  
        query = expr(query) if isinstance(query, str) else query
        if not pl_bc_entails(kb, query):
            return []
        proofs = _backward_state(kb)['proofs']
        output, visited, stack = [], set(), [(query, False)]
        while stack:
            goal, ready = stack.pop()
            if goal in visited:
                continue
            premises = proofs[goal]
            if ready:
                visited.add(goal)
                output.append({'conclusion': goal, 'premises': premises})
            else:
                stack.append((goal, True))
                stack.extend((p, False) for p in reversed(premises) if p not in visited)
        return output
    
    
    def solve_full_grid_bc(n, box_h, box_w, givens):
        
        kb = build_definite_kb(n, box_h, box_w, givens)
        grid = {}
        for r in range(1, n + 1):
            for c in range(1, n + 1):
                for v in range(1, n + 1):
                    if pl_bc_entails(kb, atom('Is', r, c, v)):
                        grid[r, c] = v
                        break
        return _check_grid(grid, n, box_h, box_w, givens)

"""