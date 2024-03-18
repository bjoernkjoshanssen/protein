import Mathlib.Computability.NFA
import Mathlib.Data.Nat.Basic
import Mathlib.MeasureTheory.Constructions.Prod.Basic
import Std.Data.Nat.Lemmas
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Vector.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Digits
import MyProject.Squarefree
import MyProject.MonoPred
set_option tactic.hygienic false
set_option maxHeartbeats 3000000

/- We formally verify the method known as recursive backtracking
for a monotone predicate P and another predicate Q at the leaves. -/

-- A vector of length L monus k, thought of as a possible suffix for a word of length L
-- in which the first k bits are unspecified
-- For example, a Gap 10 10 has length 10 - 10.
def Gap (b L k : ℕ) : Type := Vector (Fin b) (L - k)

/- Note that Gap_cons requires the use of L.succ instead of just L. -/
def Gap_cons {n L b:ℕ} (a:Fin b) (w : Gap b L.succ n.succ)
                  (h: ¬ n ≥ L.succ) : Gap b L.succ n
  := ⟨a :: w.1, by {rw [List.length_cons];simp;exact (Nat.succ_sub (Nat.not_lt.mp h)).symm}⟩

def Gap_nil {k b L : ℕ} (h : k ≥ L) : Gap b L k
  := ⟨List.nil, by {rw [Nat.sub_eq_zero_of_le h];rfl}⟩


def Gap_nil'  (b n : ℕ)             : Gap b n n := ⟨[], by simp⟩

def num_by_backtracking {k b L:ℕ}
  (P: List (Fin b) → Prop) [DecidablePred P]
  (Q: List (Fin b) → Prop) [DecidablePred Q]
  (w : Gap b L.succ k) : ℕ :=
by {
  induction k
  exact ((ite (P w.1 ∧ Q w.1) 1 0))   /- Base case -/
  exact  /- Inductive case -/
    (ite (P w.1)) (dite (n ≥ L.succ)
      (λ h ↦                             n_ih (Gap_nil        h) )
      (λ h ↦ List.sum (List.ofFn (λ a ↦ (n_ih (Gap_cons a w h)))))
    ) 0
}


theorem cons_suffix {b:ℕ}
{L n_1: ℕ} {a : Fin b}
(h: ¬n_1 ≥ Nat.succ L)
(w: Vector (Fin b) (Nat.succ L -  (Nat.succ n_1)))

: w.1 <:+ (Gap_cons a w h).1 := by {
  exists [a];
}

lemma still_does_not_hold
{b L z: ℕ }
{M: MonoPred b}
{w: Gap b (Nat.succ L) (Nat.succ z)}
(h: ¬z ≥ Nat.succ L)
(H: ¬M.P w.1)
: ∀ a, ¬ M.P (Gap_cons a w h).1 := by
  intro a hc; exact H (M.preserved_under_suffixes w.1 (Gap_cons a w h).1 (cons_suffix _ _) hc)

lemma still_does_not_hold''
{b L z: ℕ }
{M: MonoPred b}
{w: Gap b (Nat.succ L) (Nat.succ z)}
(h: ¬z ≥ Nat.succ L)
(H: ¬(M.P w.1))
: ∀ a, ¬ (M.P (Gap_cons a w h).1 ∧ M.Q (Gap_cons a w h).1) := by
  intro a hc;
  exact H (M.preserved_under_suffixes w.1 (Gap_cons a w h).1 (cons_suffix _ _) hc.1)

theorem branch_out'' (b:ℕ) {n L:ℕ} (M:MonoPred b)[DecidablePred M.P][DecidablePred M.Q]
(hnL: ¬ n ≥ L.succ) (w : Gap b L.succ n.succ) :
  num_by_backtracking M.P M.Q (w)
  = List.sum (List.ofFn (λ a ↦ num_by_backtracking M.P M.Q (Gap_cons a w hnL)))
  := by
  cases n -- Note: "induction n" not needed
  -- Zero case:
  unfold num_by_backtracking
  simp
  intro H

  symm
  have : List.ofFn (fun a => ite (
    M.P (Gap_cons a w (by linarith)).1
    ∧
    M.Q (Gap_cons a w (by linarith)).1
  ) 1 0)
        = List.replicate b 0 := by
    refine List.eq_replicate.mpr ?_
    constructor
    . simp
    intro i hi
    simp at hi
    rw [List.mem_iff_get] at hi
    rcases hi with ⟨n,hn⟩
    simp at hn
    rw [if_neg (still_does_not_hold'' _ H _)] at hn
    . exact hn.symm
  rw [this]
  . apply List.sum_const_nat b 0
    -- Successor case:
  unfold num_by_backtracking
  simp
  by_cases H : (M.P w.1)
  rw [if_pos H,dif_neg hnL]

  rw [if_neg H]
  symm
  let Recu := Nat.rec
          (motive := fun {k} => Gap b (Nat.succ L) k → ℕ)
          (fun w => ite (M.P w.1 ∧ M.Q w.1) 1 0) -- needs a Q
          (fun n n_ih w =>
            if M.P w.1 then -- doesn't need a Q
              if h : Nat.succ L ≤ n then        n_ih (Gap_nil h)
              else List.sum (List.ofFn fun a => n_ih (Gap_cons a w h))
            else 0)
  have : (List.ofFn fun a =>
    if M.P (Gap_cons a w hnL).1
    then
      if h : Nat.succ L ≤ n_1 then
        Recu n_1 (Gap_nil h)
      else
        List.sum (List.ofFn fun a_1 => Recu n_1 (Gap_cons a_1 (Gap_cons a w hnL) h))
    else 0)
    = List.replicate b 0 := by {
    refine List.eq_replicate.mpr ?_
    constructor
    . simp
    intro i hi
    simp at hi
    rw [List.mem_iff_get] at hi
    rcases hi with ⟨n,hn⟩
    simp at hn
    rw [if_neg (still_does_not_hold _ H _)] at hn
    . exact hn.symm
  }
  rw [this]
  apply List.sum_const_nat b 0

theorem subtype_ext {α:Type} (P Q:α→ Prop) (h : ∀ x, P x ↔ Q x):
 {x : α // P x} =  {x : α // Q x} :=  congrArg Subtype (funext (fun x => propext (h x)))

theorem fincard_ext {α:Type} (P Q:α→ Prop) (h : ∀ x, P x ↔ Q x)
  [Fintype {x : α // P x}][Fintype {x : α // Q x}] :
  Fintype.card {x : α // P x} = Fintype.card {x : α // Q x} := by simp_rw [subtype_ext P Q h]

theorem Vector_eq_of_suffix_of_length_eq {L b:ℕ} {w : Vector (Fin b) L}
{v : Vector (Fin b) L} (hv : w.1 <:+ v.1) : w.1 = v.1
:= List.eq_of_suffix_of_length_eq hv (by {rw [v.2,w.2]})

theorem disjoint_branch''  {L b: ℕ} {i j : Fin b} (hp: i ≠ j) {M:MonoPred b} --[DecidablePred M.P]
  {n:ℕ} (w: Vector (Fin b) (L.succ-n.succ)) (h : ¬ n ≥ L.succ)
  :
  Disjoint (λ v  : Vector (Fin b) L.succ ↦ (M.P v.1 ∧ M.Q v.1) ∧ (Gap_cons i w h).1 <:+ v.1 )
           (λ v  : Vector (Fin b) L.succ ↦ (M.P v.1 ∧ M.Q v.1) ∧ (Gap_cons j w h).1 <:+ v.1 ) := by {
  intro S h0S h1S v hSv
  rcases (h0S v hSv).2 with ⟨t₁,ht₁⟩
  rcases (h1S v hSv).2 with   ⟨t₀,ht₀⟩

  have : t₁ ++ [i] ++ w.1 = t₀ ++ [j] ++ w.1 := calc
                        _ = t₁ ++ i :: w.1   := (List.append_cons t₁ i w.1).symm
                        _ = v.1              := ht₁
                        _ = t₀ ++ j :: w.1   := ht₀.symm
                        _ = _                := (List.append_cons t₀ j w.1)

  have : (t₁ ++ [i]).getLast (by simp)
       = (t₀ ++ [j]).getLast (by simp) := List.getLast_congr _ _ ((List.append_left_inj w.1).mp this)
  simp at this
  exact hp this
}

lemma list_get_ne_nil {α: Type}
{x y: List α}
(hl: List.length x < List.length y)
{t: List α}
(ht: t ++ x = y)
: t ≠ []
:= by
    intro hc; subst hc; simp at ht; subst ht; contrapose hl
    . exact Nat.lt_irrefl (List.length x)

theorem Vector_append_succ_ne_nil {L n b: ℕ}
{w: Vector (Fin b) (Nat.succ L - Nat.succ n)}
{v: Vector (Fin b) (Nat.succ L)} {t: List (Fin b)} (ht: t ++ w.1 = v.1) :
t ≠ List.nil := by
  intro hc; subst hc; simp at ht; apply congr_arg List.length at ht; simp at ht
  have : L - n ≤ L := Nat.sub_le L n; rw [ht] at this; contrapose this; exact Nat.not_succ_le_self L

theorem List_reverse_ne_nil {α : Type} {t : List α} (hlong : t ≠ List.nil) : t.reverse ≠ List.nil
  := by {
      intro hc; apply congrArg List.reverse at hc; simp at hc; tauto
    }

theorem List_reverse_cons {α : Type} {s t: List α} {a: α} (hs: t.reverse = a :: s)
: t = s.reverse ++ [a] := by
    apply congrArg List.reverse at hs
    simp at hs
    tauto

lemma prefix_of_same {L b: ℕ} (w: Vector (Fin b) L)
: ∀ x y : {v : Vector (Fin b) L // w.1 <:+ v.1}, x.1 = y.1 := by {
    intro x y
    have : x.1.1 = y.1.1 := calc
               _ = w.1   := (Vector_eq_of_suffix_of_length_eq x.2).symm
               _ = _     :=  Vector_eq_of_suffix_of_length_eq y.2
    exact SetCoe.ext this
  }

lemma list_sum_ofFn_succ {n:ℕ} (f:Fin n.succ → ℕ):
List.sum (List.ofFn (λ i ↦ f i)) = List.sum (List.ofFn (λ i : Fin n ↦ f i)) + f n := by
  repeat (rw [List.sum_ofFn])
  . simp; exact Fin.sum_univ_castSucc fun i => f i

lemma disjoint_from_last {α: Type} {n_1: ℕ} {p: Fin (Nat.succ n_1) → α → Prop}
(h: ∀ (i j : Fin (Nat.succ n_1)), i ≠ j → Disjoint (p i) (p j))
: Disjoint (λ x : α ↦ ∃ i, p (Fin.castSucc i) x) (λ x : α ↦ p (n_1) x) := by
    intro S hS₀ hS₁ x hSx
    rcases hS₀ x hSx with ⟨i,hi⟩

    let hj := hS₁ x hSx
    simp at hj
    have hi': (λ y ↦ y=x) ≤ p i   := by intro y hy; rw [hy]; norm_cast
    have hj': (λ y ↦ y=x) ≤ p n_1 := by intro y hy; rw [hy]; simp; tauto
    have : (Fin.castSucc i).1 ≠ n_1 := by {
      intro hc; simp at hc; let G := i.2; rw [hc] at G; exact LT.lt.false G
    }
    have : (Fin.castSucc i) ≠ n_1 := by {
      intro hc; let G := congr_arg (λ x ↦ x.1) hc; simp at G; exact this G
    }
    have : (@Nat.cast (Fin (Nat.succ n_1)) Semiring.toNatCast ↑i : Fin (Nat.succ n_1)) ≠ n_1 := by norm_cast
    exact h i n_1 this hi' hj' x rfl


def getFin {n_1 : ℕ} {i: Fin (Nat.succ n_1)} (hin: ¬i = ↑n_1) : Fin n_1 := by {
  have : i.1 < n_1 := by {
    cases (Nat.lt_or_eq_of_le (Fin.is_le i)); exact h; exfalso
    have : i = n_1 := by apply Fin.ext; rw [h]; simp
    exact hin this
  }
  exact ⟨i.1,this⟩
}

lemma distinguish_from_last {α: Type} {n_1: ℕ} {p: Fin (Nat.succ n_1) → α → Prop} (x : α)
: (∃ i, p (Fin.castSucc i) x) ∨ p (↑n_1) x ↔ ∃ i, p i x := by
  constructor; intro ha; cases ha; rcases h with ⟨i,hi⟩
  exists i; norm_cast
  exists n_1; intro ha; rcases ha with ⟨i,hi⟩; by_cases hin:(i=n_1)
  right; rw [← hin]; exact hi; left
  exists getFin hin -- ⟨i.1,_⟩

def getFin_pred {n_1:ℕ} (i: Fin n_1.pred) : i < n_1 := calc
  i.1 < n_1.pred := i.2
  _   ≤ n_1      := Nat.pred_le n_1

lemma disjoint_cast {α: Type} {n_1: ℕ} {p: Fin (Nat.succ n_1) → α → Prop}
(h: ∀ (i j : Fin (Nat.succ n_1)), i ≠ j → Disjoint (p i) (p j))
 : (∀ (i j : Fin n_1),            i ≠ j → Disjoint (p (Fin.castSucc i)) (p (Fin.castSucc j)))
:= by
  intro i j hij
  have : Fin.castSucc i ≠ Fin.castSucc j := by intro hc; apply Fin.castSucc_inj.mp at hc; tauto
  have : (@Nat.cast (Fin (Nat.succ n_1)) Semiring.toNatCast ↑i : Fin (Nat.succ n_1))
       ≠ (@Nat.cast (Fin (Nat.succ n_1)) Semiring.toNatCast ↑j : Fin (Nat.succ n_1)) := by
    intro hc; simp at hc; exfalso; exact this hc
  let G := h i j this
  norm_cast at G

lemma input_to_fintype {α:Type} [Fintype α]
  {n_1 : ℕ} {p : Fin n_1.succ → α → Prop}
  [DecidablePred fun x => ∃ i : Fin n_1, p (Fin.castSucc i) x]
  (x : α)
  : x ∈ (Finset.filter (fun x => ∃ i : Fin n_1, p (Fin.castSucc i) x) Finset.univ)
                               ↔ ∃ i,           p (Fin.castSucc i) x
  := by {
    constructor
    intro hxs; exact (Finset.mem_filter.mp hxs).2
    intro h;   exact Finset.mem_filter.mpr (And.intro (Finset.mem_univ x) h)
  }

theorem Fintype_card_subtype_or_disjoint' {α:Type} [Fintype α]
{n:ℕ} (p : Fin n → α → Prop) -- January 30, 2024.
[Fintype {x:α // ∃ i, p i x}] [∀ i, Fintype {x:α // p i x}]
[DecidablePred fun x => ∃ i : Fin n.pred, p ⟨i,getFin_pred i⟩ x]
(h : ∀ i j, i ≠ j → Disjoint (p i) (p j))
:
List.sum (List.ofFn (λ i ↦ Fintype.card {x:α // p i x}))
                         = Fintype.card {x:α // ∃ i, p i x}
:= by {
  induction n; simp
  rename_i h₀ h₁ h₂
  -- Requires several decidability facts:
  have : DecidablePred fun x => ∃ i, p (Fin.castSucc i) x := h₂
  have : DecidablePred fun x : α => ∃ i : Fin n_1.pred, (fun i a => p (Fin.castSucc i) a) ⟨i.1, getFin_pred i⟩ x
    := Classical.decPred _
  have : Fintype { x : α // (∃ i, p (Fin.castSucc i) x) ∨ p (↑n_1) x } :=
    Fintype.ofFinite { x // (∃ i, p (Fin.castSucc i) x) ∨ p (↑n_1) x }

  rw [list_sum_ofFn_succ]
  norm_cast
  rw [
    n_ih (λ i a ↦ p (Fin.castSucc i) a) (disjoint_cast h),
    ← Fintype.card_subtype_or_disjoint _ _ (disjoint_from_last h)
  ]; apply fincard_ext; exact distinguish_from_last
}


lemma get_union {α :Type} {x y : List α} (h : x <:+ y) (hl : x.length < y.length) :
∃ a : α, a :: x <:+ y := by
  rcases h with ⟨t,ht⟩;
  rcases (List.exists_cons_of_ne_nil (List_reverse_ne_nil (list_get_ne_nil hl ht))) with ⟨a,ha⟩;
  rcases ha with ⟨s,hs⟩; exists a; exists s.reverse
  rw [List_reverse_cons hs] at ht; rw [← ht]
  . simp

instance {b L:ℕ} : Fintype (Gap b (Nat.succ L) 0) := by
  unfold Gap
  exact Vector.fintype

theorem distribute_prop {α : Type} (P Q : Prop) {S : Prop} {s : α → Prop}
     (h : S ↔ ∃ a, s a) :
  P ∧ Q ∧ S ↔ ∃ a, P ∧ Q ∧ s a := by
    constructor; intro h₀; rcases h.mp h₀.2.2 with ⟨a, ha⟩; exists a; tauto; intro h₀
    rcases h₀ with ⟨a,ha⟩;constructor;tauto;constructor;tauto; have : ∃ a, s a := by exists a; tauto
    rw [← h] at this; tauto

theorem suffix_cons
{b L: ℕ}
{n: ℕ}
(w: Gap b (Nat.succ L) (Nat.succ n))
: ∀ (v : Gap b (Nat.succ L) 0), w.1 <:+ v.1 ↔ ∃ a, a :: w.1 <:+ v.1
:= by
    intro v; constructor
    intro h
    have : w.1.length < v.1.length := by
      rw [w.2,v.2]; simp
      . calc
        _ ≤ L      := Nat.sub_le L n
        _ < L.succ := Nat.lt.base L
    . exact get_union h this
    intro h
    rcases h with ⟨a,ha⟩; rcases ha with ⟨t,ht⟩; exists t ++ [a]; rw [← ht]
    . simp

theorem backtracking_verification {k b L:ℕ}
/- This verifies recursive backtracking for b-ary trees with monotone predicates P,
   with a non-monotone Q at the leaves. January 31, 2024.
-/
  (bound : k ≤ L.succ) (M:MonoPred b)
  [DecidablePred M.P] [DecidablePred M.Q]
  (w : Vector (Fin b) (L.succ-k)):
  Fintype.card {
    v : Vector (Fin b) L.succ // (M.P v.1 ∧ M.Q v.1) ∧ w.1 <:+ v.1
  }
  = num_by_backtracking M.P M.Q w
  := by
  induction k -- Since num_by_backtracking was defined by recursion, so is the proof.
  unfold num_by_backtracking; simp
  by_cases hs : (M.P w.1 ∧ M.Q w.1)
  rw [if_pos hs]
  have := subsingleton_iff.mpr (
    λ x y : {v : Vector (Fin b) L.succ // (M.P v.1 ∧ M.Q v.1) ∧ w.1 <:+ v.1}
    ↦ SetCoe.ext (prefix_of_same w ⟨x.1,x.2.2⟩ ⟨y.1,y.2.2⟩)
  )
  have := uniqueOfSubsingleton
    (⟨w,⟨hs, List.suffix_rfl⟩⟩ : {v : Vector (Fin b) L.succ // (M.P v.1 ∧ M.Q v.1) ∧ w.1 <:+ v.1})
  . exact Fintype.card_unique

  rw [if_neg hs]
  have : ∀ v: Vector (Fin b) L.succ ,¬ ((M.P v.1 ∧ M.Q v.1) ∧ w.1 <:+ v.1) := by {
    intro v hc
    have : w = v := SetCoe.ext (Vector_eq_of_suffix_of_length_eq hc.2)
    subst this; tauto
  }
  have := Subtype.isEmpty_of_false this
  . exact Fintype.card_eq_zero
  -- Inductive step:
  by_cases case : (n ≥ L.succ)
  exfalso
  have : n.succ ≤ n := calc
              _ ≤ L.succ := bound
              _ ≤ n      := case
  . exact Nat.not_succ_le_self n this
  -- Nontrivial case:
  have hcard : List.sum (List.ofFn (λ i ↦
       Fintype.card {v:Vector (Fin b) L.succ //      (M.P v.1 ∧ M.Q v.1) ∧ (Gap_cons i w case).1 <:+ v.1}
  )) = Fintype.card {v:Vector (Fin b) L.succ // ∃ i, (M.P v.1 ∧ M.Q v.1) ∧ (Gap_cons i w case).1 <:+ v.1} :=
    Fintype_card_subtype_or_disjoint' _ (λ _ _ hij ↦ disjoint_branch'' hij w case)
  simp at hcard;
  rw [
    branch_out'' _ _ case,
    ← funext (λ i : Fin b ↦ n_ih (Nat.le_of_lt bound) (Gap_cons i w case)),
    hcard
  ];
  apply fincard_ext; intro x;
  . rw [and_assoc, distribute_prop (M.P x.1) (M.Q x.1) (suffix_cons w x)]; tauto

instance (k b L f:ℕ)
(bound : k ≤ L.succ) (M:MonoPred b) [DecidablePred M.P] [DecidablePred M.Q]
(w : Vector (Fin b) (L.succ-k)):
  Decidable (Fintype.card {v : Vector (Fin b) L.succ // (M.P v.1 ∧ M.Q v.1) ∧ w.1 <:+ v.1} =f)
:= decidable_of_iff (num_by_backtracking M.P M.Q w = f) (by {
  constructor
  intro h; rw [← h]; exact backtracking_verification bound _ _
  intro h; rw [← h]; exact (backtracking_verification bound _ _).symm
})

#eval Fintype.card {v : Vector (Fin 3) 3 // (squarefree v.1 ∧ True) ∧ [] <:+ v.1}
example :
Fintype.card {v : Vector (Fin 3) 3 // (squarefree v.1 ∧ True) ∧ [] <:+ v.1} = 12 := by decide

instance : DecidableEq (Gap b (Nat.succ L) 0)
:= by
  unfold Gap
  exact Vector.instDecidableEqVector

def those_with_suffix' {k b :ℕ} {L:ℕ} (P: List (Fin b) → Prop) [DecidablePred P]
  (Q: List (Fin b) → Prop) [DecidablePred Q] (w : Gap b L.succ k) : Finset (Gap b L.succ 0) :=
by {
  induction k
  . exact ((ite (P w.1 ∧ Q w.1) {w} ∅))
  . exact
      (ite (P w.1))
      (
        dite (n ≥ L.succ)
        (λ h ↦ n_ih (Gap_nil h))
        (
          λ h ↦ Finset.biUnion (Finset.univ : Finset (Fin b)) (
            (λ a ↦ (n_ih (Gap_cons a w h)))
          )
        )
      )
      ∅
}

theorem branch_out_set (b:ℕ) {n L:ℕ}
{M: MonoPred b} [DecidablePred M.P]
[DecidablePred M.Q]
(hnL: ¬ n ≥ L.succ) (w : Gap b L.succ n.succ) :
  those_with_suffix' M.P M.Q (w)
  = Finset.biUnion (Finset.univ : Finset (Fin b)) (λ a ↦ those_with_suffix' M.P M.Q (Gap_cons a w hnL))
:= by
  cases n -- induction not needed
  unfold those_with_suffix'; simp; intro H; symm
  have : ∀ a, ite (M.P (Gap_cons a w hnL).1 ∧ M.Q (Gap_cons a w hnL).1)
      ({Gap_cons a w hnL} : Finset _) ∅ = ∅ := by
      intro a
      have : ¬ M.P (Gap_cons a w hnL).1 := still_does_not_hold _ H _
      have : ¬ (M.P (Gap_cons a w hnL).1 ∧ M.Q (Gap_cons a w hnL).1) := by tauto
      rw [if_neg this]
  rw [funext this]
  simp
  apply Finset.ext;intro v;constructor;
  . intro h;simp at h
  . intro h;simp; tauto
  -- Successor case
  unfold those_with_suffix'; simp
  by_cases H : (M.P w.1)
  . rw [if_pos H,dif_neg hnL]
  rw [if_neg H]; symm
  apply Finset.ext; intro v; constructor; intro hv; contrapose hv; simp; intro i
  rw [if_neg (still_does_not_hold _ H _)]
  . intro hv; simp at hv
  . intro hv; simp at hv


theorem filter_suffix_empty
{b L: ℕ}
{P Q : List (Fin b) → Prop}
[DecidablePred P]
[DecidablePred Q]
(w: Gap b (Nat.succ L) Nat.zero)
(holds: ¬(P w.1 ∧ Q w.1))
: ∅ = Finset.filter (fun v : Gap b L.succ 0 => P v.1 ∧ Q v.1 ∧ w.1 <:+ v.1) Finset.univ
:= by
  apply Finset.ext
  intro a;
  constructor;
  . intro ha; simp at ha;
  intro ha; simp at ha;
  have : w.1 = a.1 := List.eq_of_suffix_of_length_eq ha.2.2 (by {rw [w.2,a.2]})
  rw [this] at holds
  . tauto

theorem filter_suffix_singleton
{b L: ℕ}
{P Q : List (Fin b) → Prop}
[DecidablePred P]
[DecidablePred Q]
(w: Gap b (Nat.succ L) Nat.zero)
(holds: (P w.1 ∧ Q w.1))
: {w} = Finset.filter (fun v : Gap b L.succ 0 => P v.1 ∧ Q v.1 ∧ w.1 <:+ v.1) Finset.univ
:= by
  apply Finset.ext
  intro a; constructor; intro ha; simp at ha; subst ha; simp; constructor; tauto; constructor
  tauto;
  . exists []
  simp;intro;intro;intro hs;symm
  have : w.1 = a.1 := List.eq_of_suffix_of_length_eq hs (by {rw [w.2,a.2]})
  . exact Vector.eq w a this


theorem verify_those_with_suffix' {k b :ℕ} {L:ℕ} (bound : k ≤ L.succ)
{M:MonoPred b}
[DecidablePred M.P]
[DecidablePred M.Q] (w : Gap b L.succ k) :
  those_with_suffix' M.P M.Q w = Finset.filter (
    λ v : Gap b L.succ 0 ↦ M.P v.1 ∧ M.Q v.1 ∧ w.1 <:+ v.1
  ) Finset.univ := by
  induction k
  unfold those_with_suffix'
  simp
  by_cases holds: (M.P w.1 ∧ M.Q w.1)
  . rw [if_pos holds]; exact filter_suffix_singleton _ holds
  . rw [if_neg holds]; exact filter_suffix_empty _ holds

  -- Inductive step
  by_cases hLn: (L.succ ≤ n) -- hLn some places called "case"
  have : n.succ ≤ n := calc
              _ ≤ L.succ := bound
              _ ≤ n      := hLn
  . exfalso; exact Nat.not_succ_le_self n this

  let U := (Finset.univ : Finset (Gap b L.succ 0))

  have h₂ : Finset.filter (fun v => M.P v.1 ∧ M.Q v.1 ∧      w.1 <:+ v.1) U = Finset.biUnion (Finset.univ : Finset (Fin b))
     (λ a ↦ Finset.filter (fun v => M.P v.1 ∧ M.Q v.1 ∧ a :: w.1 <:+ v.1) U) := by calc
    _ = Finset.filter (fun v => ∃ a, M.P v.1 ∧ M.Q v.1 ∧ a :: w.1 <:+ v.1) U := by
      simp_rw [funext (λ a ↦ propext (distribute_prop _ _ (suffix_cons _ a)))]
    _ = _                                                                    := by apply Finset.ext; intro v; simp;

  . rw [branch_out_set,h₂,funext (λ a ↦ n_ih (Nat.le_of_lt bound) (Gap_cons a w hLn))];rfl
