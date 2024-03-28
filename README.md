# protein
Lean and Python code for "Nonmonotonicity of the value function in HP protein folding models"

- `MonoPred` (introduce the idea of a monotone predicate `P` together with an additional predicate `Q` at the leaves, for use in backtracking)
  * `BacktrackingVerification` (verifying that computations using `by decide` do in fact count the number of words where `P ∧ Q` hold)
    - `StecherConjecture_SpringBreak2024` (introduce protein folding basics and use backtracking to calculate folding scores)
      * `StecherConjecture-GroupComputations` (some not-very-important calculations)
      * `StecherConjectureF`  (using `Fin l → β` types instead of `Vector β l`)
        - `StecherConjecture-pathF` (using infinity to define path)
        - `StecherConjecture-pathF'` (purely finite version of path)
      * `Handshake` (prove upper bound `l*b/2` on the score, where `l` is word length and `b` is number of moves, using Handshake Lemma)
