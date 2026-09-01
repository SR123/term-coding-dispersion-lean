#!/usr/bin/env python3
"""Exhaustively verify the four-term relay values for alphabets 2 and 3."""

from itertools import product


def relay_image_size(table: tuple[int, ...], n: int) -> int:
    """Return the image size of T_f for a row-major binary operation table."""
    image = {
        (
            table[x1 * n + y1],
            table[x1 * n + y2],
            table[x2 * n + y1],
            table[x2 * n + y2],
        )
        for x1, x2, y1, y2 in product(range(n), repeat=4)
    }
    return len(image)


def exhaustive_optimum(n: int) -> tuple[int, tuple[int, ...]]:
    """Return the optimum and the first row-major table attaining it."""
    best = -1
    first_table: tuple[int, ...] | None = None
    for table in product(range(n), repeat=n * n):
        score = relay_image_size(table, n)
        if score > best:
            best = score
            first_table = table
    assert first_table is not None
    return best, first_table


def main() -> None:
    expected = {
        2: (10, (0, 0, 0, 1)),
        3: (51, (0, 0, 1, 0, 2, 2, 1, 2, 1)),
    }
    for n, (expected_score, displayed_table) in expected.items():
        score, first_table = exhaustive_optimum(n)
        assert score == expected_score
        assert relay_image_size(displayed_table, n) == expected_score
        print(f"n={n}: optimum={score}; first optimal table={first_table}")


if __name__ == "__main__":
    main()

