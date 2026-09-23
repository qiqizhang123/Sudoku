import json
import time
import streamlit as st

from sudoku_solver import (
    atom,
    build_definite_kb,
    solve_full_grid_fc,
    solve_full_grid_bc,
    pl_bc_entails
)


st.set_page_config(
    page_title="Sudoku Solver",
    page_icon="🧩"
)

st.title("Sudoku Solver")


# load puzzles
with open("puzzles.json", "r") as f:
    data = json.load(f)

n = data["n"]
box_h = data["box_h"]
box_w = data["box_w"]
puzzles = data["puzzles"]


def convert_givens(raw_givens):
    givens = {}

    for key, value in raw_givens.items():
        r, c = map(int, key.split("_"))
        givens[(r, c)] = value

    return givens


def parse_atom(x):
    name = x.op

    if name.startswith("Is"):
        kind = "Is"
        rest = name[2:]

    elif name.startswith("Not"):
        kind = "Not"
        rest = name[3:]

    else:
        return None

    parts = rest.split("_")

    if len(parts) != 3:
        return None

    r, c, v = map(int, parts)

    return kind, r, c, v


def explain_step(conclusion, premises):
    result = parse_atom(conclusion)

    if result is None:
        return str(conclusion)

    kind, r, c, v = result

    if not premises:
        return f"Cell ({r}, {c}) = {v} is a given."

    parsed_premises = [parse_atom(p) for p in premises]

    if kind == "Not" and len(premises) == 1:
        source = parsed_premises[0]

        if source is not None and source[0] == "Is":
            _, sr, sc, sv = source

            if sr == r and sc == c:
                return (
                    f"Cell ({r}, {c}) is already {sv}, "
                    f"so it cannot be {v}."
                )

            if sr == r:
                return (
                    f"Cell ({sr}, {sc}) = {sv}. "
                    f"Since it is in the same row as ({r}, {c}), "
                    f"value {v} is eliminated from ({r}, {c})."
                )

            if sc == c:
                return (
                    f"Cell ({sr}, {sc}) = {sv}. "
                    f"Since it is in the same column as ({r}, {c}), "
                    f"value {v} is eliminated from ({r}, {c})."
                )

            return (
                f"Cell ({sr}, {sc}) = {sv}. "
                f"Since it shares the same box with ({r}, {c}), "
                f"value {v} is eliminated from ({r}, {c})."
            )

    if kind == "Is":
        eliminated = []

        for p in parsed_premises:
            if p is not None and p[0] == "Not":
                eliminated.append(p[3])

        if eliminated:
            eliminated.sort()
            values_text = ", ".join(str(x) for x in eliminated)

            return (
                f"Values {values_text} have been eliminated from "
                f"cell ({r}, {c}). Therefore, the only remaining "
                f"value is {v}."
            )

        return f"Therefore, cell ({r}, {c}) is {v}."

    return f"Therefore, cell ({r}, {c}) is not {v}."


def get_reasoning_steps(kb, query):
    state = getattr(kb, "_bc_state", None)

    if state is None:
        return []

    proofs = state.get("proofs", {})

    if query not in proofs:
        return []

    steps = []
    visited = set()

    def visit(goal):
        if goal in visited or goal not in proofs:
            return

        premises = proofs[goal]

        for premise in premises:
            visit(premise)

        visited.add(goal)
        steps.append((goal, premises))

    visit(query)

    return steps


def show_solution_board(values, givens):
    html = """
    <style>
    .sudoku-board {
        border-collapse: collapse;
        margin: 10px 0 25px 0;
    }

    .sudoku-board td {
        width: 50px;
        height: 50px;
        text-align: center;
        vertical-align: middle;
        font-size: 22px;
        border: 1px solid #777;
    }

    .sudoku-board .given {
        font-weight: bold;
        background-color: #e8e8e8;
        color: #111;
    }

    .sudoku-board .solved {
        font-weight: normal;
    }
    </style>

    <table class="sudoku-board">
    """

    for r in range(1, n + 1):
        html += "<tr>"

        for c in range(1, n + 1):
            value = values.get((r, c), "")

            if (r, c) in givens:
                cell_class = "given"
            else:
                cell_class = "solved"

            styles = []

            if (r - 1) % box_h == 0:
                styles.append("border-top: 3px solid #777")

            if (c - 1) % box_w == 0:
                styles.append("border-left: 3px solid #777")

            if r == n:
                styles.append("border-bottom: 3px solid #777")

            if c == n:
                styles.append("border-right: 3px solid #777")

            style = "; ".join(styles)

            html += (
                f'<td class="{cell_class}" style="{style}">'
                f'{value}'
                f'</td>'
            )

        html += "</tr>"

    html += "</table>"

    st.markdown(html, unsafe_allow_html=True)


def show_editable_board(givens, puzzle_index):
    entries = {}

    for r in range(1, n + 1):
        columns = st.columns(n, gap="small")

        for c in range(1, n + 1):
            cell = (r, c)

            with columns[c - 1]:

                if cell in givens:
                    st.markdown(
                        f"""
                        <div style="
                            height: 42px;
                            display: flex;
                            align-items: center;
                            justify-content: center;
                            border: 1px solid #777;
                            background-color: #e8e8e8;
                            color: #111;
                            font-size: 20px;
                            font-weight: bold;
                            border-radius: 4px;
                        ">
                            {givens[cell]}
                        </div>
                        """,
                        unsafe_allow_html=True
                    )

                else:
                    entered = st.text_input(
                        f"R{r}C{c}",
                        max_chars=1,
                        key=f"p{puzzle_index}_r{r}_c{c}",
                        label_visibility="collapsed"
                    )

                    if entered.isdigit():
                        number = int(entered)

                        if 1 <= number <= n:
                            entries[cell] = number

    return entries


# choose puzzle
puzzle_index = st.selectbox(
    "Choose a puzzle",
    range(len(puzzles)),
    format_func=lambda i: f"Puzzle {i + 1}"
)

raw_givens = puzzles[puzzle_index]["givens"]
givens = convert_givens(raw_givens)


# editable puzzle
st.subheader("Puzzle")

st.caption(
    "Given cells are locked. Enter a value from 1 to 9 in any empty cell."
)

user_entries = show_editable_board(
    givens,
    puzzle_index
)


# check values entered directly on the board
if st.button("Check My Entries"):

    if not user_entries:
        st.info("Enter at least one value in an empty cell first.")

    else:
        kb = build_definite_kb(
            n,
            box_h,
            box_w,
            givens
        )

        correct_count = 0

        for (r, c), v in user_entries.items():
            query = atom("Is", r, c, v)
            result = pl_bc_entails(kb, query)

            if result:
                st.success(
                    f"Cell ({r}, {c}) = {v} can be proved."
                )
                correct_count += 1
            else:
                st.error(
                    f"Cell ({r}, {c}) = {v} cannot be proved."
                )

        st.write(
            f"{correct_count} of {len(user_entries)} entered values "
            f"were proved by the knowledge base."
        )


st.divider()


# full-grid solver
st.subheader("AI Solver")

algorithm = st.radio(
    "Algorithm",
    [
        "Forward Chaining",
        "Backward Chaining"
    ]
)

if st.button("Solve"):

    start = time.perf_counter()

    if algorithm == "Forward Chaining":
        solution = solve_full_grid_fc(
            n,
            box_h,
            box_w,
            givens
        )

    else:
        solution = solve_full_grid_bc(
            n,
            box_h,
            box_w,
            givens
        )

    elapsed = time.perf_counter() - start

    st.subheader("Solution")

    show_solution_board(
        solution,
        givens
    )

    st.write(
        f"Time: {elapsed:.4f} seconds"
    )


st.divider()


# targeted query
st.subheader("Check a Cell")

st.write(
    "Test whether a particular value can be proved "
    "using backward chaining."
)

col1, col2, col3 = st.columns(3)

with col1:
    row = st.number_input(
        "Row",
        min_value=1,
        max_value=n,
        value=1
    )

with col2:
    column = st.number_input(
        "Column",
        min_value=1,
        max_value=n,
        value=1
    )

with col3:
    value = st.number_input(
        "Value",
        min_value=1,
        max_value=n,
        value=1
    )


if st.button("Check"):

    kb = build_definite_kb(
        n,
        box_h,
        box_w,
        givens
    )

    query = atom(
        "Is",
        int(row),
        int(column),
        int(value)
    )

    result = pl_bc_entails(
        kb,
        query
    )

    st.write("Result:", result)

    if result:
        steps = get_reasoning_steps(
            kb,
            query
        )

        st.subheader("Reasoning Trace")

        for i, (conclusion, premises) in enumerate(
            steps,
            start=1
        ):

            with st.expander(
                f"Step {i}",
                expanded=(i == len(steps))
            ):
                st.write(
                    explain_step(
                        conclusion,
                        premises
                    )
                )

    else:
        st.info(
            "The selected value cannot be proved "
            "from the current knowledge base."
        )