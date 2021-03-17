# Formalized mathematics
This repository contains various mathematical theorems that I've formalized in [Lean][wi:lean], an interactive theorem prover. Below is a list of the different parts and the corresponding files.

- **Euler's Continued Fraction Formula**

    `src/ecff`
    
    We have a full proof (`euler_cff`) of [Euler's Continued Fraction Formula][ecff] using continued fractions from mathlib. The current theorem and proof is a little complicated as we're working over sequences; applications may want lists instead.

    The statement of the formalized theorem has a criteria that is usually not assumed in the normal theorem: no denominator is zero.

- **Chromatic number of a space**

    `src/chromatic`

    This is an attempt to formalize the [Hadwiger–Nelson problem][wi:hadwidger] (also knowns as the chromatic number of the plane).

    The main file is `chromatic.lean`.
    There we define the general problem of proving if a given space can be colored using `n` colors while avoiding monochrome distances in a given set `D`. This is defined as `space_colorable`. In the same file we prove that the real line can be colored using two colors while avoiding monochrome unit distances (`colorable_real_line_avoiding_one_with_two`).

    No bounds on the chromatic number of the plane have been formalized yet.

[wi:lean]: https://en.wikipedia.org/wiki/Lean_(proof_assistant)
[wi:hadwidger]: https://en.wikipedia.org/wiki/Hadwiger–Nelson_problem
[ecff]: https://en.wikipedia.org/wiki/Euler%27s_continued_fraction_formula