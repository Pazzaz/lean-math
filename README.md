# Chromatic number of a space formalized in Lean

This is an attempt to formalize the [Hadwiger–Nelson_problem][wi:hadwidger] (also knowns as the chromatic number of the plane) in [Lean][wi:lean], an interactive theorem prover.

The main file is `src/chromatic.lean`.
There we define the general problem of proving if a given space can be colored using `n` colors while avoiding monochrome distances in a given set `D`. This is defined as `space_colorable`. In the same file we prove that the real line can be colored using two colors while avoiding monochrome unit distances (`colorable_real_line_avoiding_one_with_two`).

No bounds on the chromatic number of the plane have been formalized yet.

[wi:hadwidger]: https://en.wikipedia.org/wiki/Hadwiger–Nelson_problem
[wi:lean]: https://en.wikipedia.org/wiki/Lean_(proof_assistant)

