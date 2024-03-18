import Mathlib.Computability.NFA
import Mathlib.Data.Nat.Basic
import Mathlib.MeasureTheory.Constructions.Prod.Basic
import Std.Data.Nat.Lemmas
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Vector.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Digits

structure MonoPred (b:ℕ) where
  P : List (Fin b) → Prop
  preserved_under_suffixes (u v : List (Fin b)): u <:+ v → P v → P u
  Q (l: List (Fin b)) : Prop := True -- we can specify an extra condition that is not monotone

structure MonoPred_unverified (b:ℕ) where
  P : List (Fin b) → Prop
  Q : List (Fin b) → Prop := λ _ ↦ True -- we can specify an extra condition that is not monotone
