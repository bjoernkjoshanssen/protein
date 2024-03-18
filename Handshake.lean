import Mathlib.Tactic
import MyProject.StecherConjecture_SpringBreak2024
open Finset
set_option tactic.hygienic false


theorem disjoint_asymm {α:Type} [Fintype α]
[DecidableEq α]
(P Q :α → α → Prop)
[DecidablePred fun a : α × α => P a.1 a.2 ∧ Q a.1 a.2]
[DecidablePred fun a : α × α => P a.1 a.2 ∧ Q a.2 a.1]
[DecidablePred fun a : α × α => P a.1 a.2 ∧ (Q a.1 a.2 ∨ Q a.2 a.1)]
[DecidablePred fun a : α × α => P a.1 a.2 ∧ (Q a.1 a.2 ∨ Q a.1 a.2)]
(hQ : IsAsymm _ Q) :
card (filter (λ a : α × α ↦ P a.1 a.2 ∧ (Q a.1 a.2 ∨ Q a.2 a.1)) univ)
= card (filter (λ a : α × α ↦ P a.1 a.2 ∧ Q a.1 a.2) univ)
+ card (filter (λ a : α × α ↦ P a.1 a.2 ∧ Q a.2 a.1) univ) := by
  have :
    (filter (λ a : α × α ↦ P a.1 a.2 ∧ (Q a.1 a.2 ∨ Q a.2 a.1)) univ)
    =
    (filter (λ a : α × α ↦ P a.1 a.2 ∧ (Q a.1 a.2 ∨ Q a.2 a.1)) univ)
    ∪
    (filter (λ a : α × α ↦ P a.1 a.2 ∧ (Q a.1 a.2 ∨ Q a.2 a.1)) univ)
    := by
      apply ext
      simp
  rw [this]
  have : Disjoint
      (filter (λ a : α × α ↦ P a.1 a.2 ∧ (Q a.2 a.1)) univ)
      (filter (λ a : α × α ↦ P a.1 a.2 ∧ (Q a.1 a.2)) univ)
    := by
      intro A h₁ h₂ a ha
      let H₁ := h₁ ha
      let H₂ := h₂ ha
      simp at H₁ H₂
      exfalso
      exact hQ.asymm _ _ H₁.2 H₂.2
  simp
  rw [Nat.add_comm, ← card_union_eq this]
  congr;apply ext;simp;intro a b;tauto

theorem disjoint_symm_asymm {α:Type} [Fintype α]
[DecidableEq α]
(P Q :α → α → Prop)
[DecidablePred fun a : α × α => P a.1 a.2 ∧ Q a.1 a.2]
[DecidablePred fun a : α × α => P a.1 a.2 ∧ Q a.2 a.1]
[DecidablePred fun a : α × α => P a.1 a.2 ∧ (Q a.1 a.2 ∨ Q a.2 a.1)]
[DecidablePred fun a : α × α => P a.1 a.2 ∧ (Q a.1 a.2 ∨ Q a.1 a.2)]
[DecidablePred fun a : α × α => P a.2 a.1 ∧ Q a.2 a.1]
(hP : Symmetric P)
(hQ : IsAsymm _ Q) :
card (filter (λ a : α × α ↦ P a.1 a.2 ∧ (Q a.1 a.2 ∨ Q a.2 a.1)) univ)
= card (filter (λ a : α × α ↦ P a.1 a.2 ∧ Q a.1 a.2) univ)
+ card (filter (λ a : α × α ↦ P a.2 a.1 ∧ Q a.2 a.1) univ) := by
  rw [disjoint_asymm P Q hQ]
  simp
  congr
  apply funext
  intro x
  simp
  intro
  constructor
  intro h
  exact hP h
  intro h
  exact hP h

theorem twice_symm_asymm {α:Type} [Fintype α]
[DecidableEq α]
(P Q :α → α → Prop)
[DecidablePred fun a : α × α => P a.1 a.2 ∧ Q a.1 a.2]
[DecidablePred fun a : α × α => P a.1 a.2 ∧ Q a.2 a.1]
[DecidablePred fun a : α × α => P a.1 a.2 ∧ (Q a.1 a.2 ∨ Q a.2 a.1)]
[DecidablePred fun a : α × α => P a.1 a.2 ∧ (Q a.1 a.2 ∨ Q a.1 a.2)]
[DecidablePred fun a : α × α => P a.2 a.1 ∧ Q a.2 a.1]
(hP : Symmetric P)
(hQ : IsAsymm _ Q) :
card (filter (λ a : α × α ↦ P a.1 a.2 ∧ (Q a.1 a.2 ∨ Q a.2 a.1)) univ)
= 2 * card (filter (λ a : α × α ↦ P a.1 a.2 ∧ Q a.1 a.2) univ) := by
  rw [disjoint_symm_asymm P Q hP hQ]
  -- simp
  let s := (filter (λ a : α × α ↦ P a.1 a.2 ∧ Q a.1 a.2) univ)
  let t := (filter (λ a : α × α ↦ P a.2 a.1 ∧ Q a.2 a.1) univ)
  let f : (a : α × α) → (a ∈ s) → α × α := λ (x,y) _ ↦ (y,x)
  have
  h₁ : ∀ (a : α×α) (ha : a ∈ s), f a ha ∈ t := by
    intro a ha
    simp
    simp at ha
    tauto
  have  h₂ : ∀ (a b : α×α) (ha : a ∈ s) (hb : b ∈ s), f a ha = f b hb → a = b := by
    intro a b ha hb hf
    simp at hf
    apply Prod.ext
    tauto;tauto
  have h₃ : ∀ b ∈ t, ∃ (a : α×α) (ha : a ∈ s), f a ha = b := by
    intro b hb
    simp
    simp at hb
    exists b.2
    exists b.1
  let R := card_congr f h₁ h₂ h₃
  rw [R]
  simp
  ring



instance separated_asymm {l:ℕ} : IsAsymm _ (λ i j : Fin l ↦ i.1.succ < j.1) := {
  asymm := by
    intro a b h hc
    have : a.1.succ < a.1 := calc
      _ < b.1      := h
      _ < b.1.succ := Nat.lt.base b.1
      _ < _        := hc
    contrapose this
    exact Nat.not_succ_lt_self
}

theorem twice_fold {l:ℕ} (P: Fin l → Fin l → Prop)
[DecidablePred fun a : (Fin l) × (Fin l)  => P a.1 a.2]
[DecidablePred fun a : (Fin l) × (Fin l)  => P a.1 a.2 ∧ (fun i j => Nat.succ ↑i < ↑j) a.1 a.2]
[DecidablePred fun a : (Fin l) × (Fin l) => P a.1 a.2 ∧ ((fun i j => Nat.succ ↑i < ↑j) a.1 a.2 ∨ (fun i j => Nat.succ ↑i < ↑j) a.2 a.1)]
[DecidablePred fun a : (Fin l) × (Fin l) => P a.1 a.2 ∧ (λ i j : Fin l ↦ i.1.succ < j.1) a.2 a.1]
[DecidablePred fun a : (Fin l) × (Fin l) => P a.1 a.2 ∧ ((λ i j : Fin l ↦ i.1.succ < j.1) a.1 a.2 ∨ (λ i j : Fin l ↦ i.1.succ < j.1) a.1 a.2)]
[DecidablePred fun a : (Fin l) × (Fin l) => P a.2 a.1 ∧ ((λ i j : Fin l ↦ i.1.succ < j.1)) a.2 a.1]
(hP: Symmetric P):
card (
  filter (
    λ a : (Fin l) × (Fin l) ↦ P a.1 a.2 ∧ (
         a.1.1.succ < a.2.1
      ∨ a.2.1.succ < a.1.1)
  )
  univ
)
= 2 * card (filter (λ a : (Fin l) × (Fin l) ↦ P a.1 a.2 ∧ a.1.1.succ < a.2.1) univ) := by

  exact twice_symm_asymm P (λ i j : Fin l ↦ i.1.succ < j.1) hP separated_asymm

open Finset
theorem twice_fold_pts  {α:Type} {β : Type} [Fintype β] (go : β → α → α) [DecidableEq α]
 {l : ℕ} (fold : Vector α l) (phobic : Vector Bool l)
(hP: Symmetric (λ i j : Fin l ↦ phobic.get i && phobic.get j && nearby go (fold.get i) (fold.get j))):
card (
  filter (
    λ a : (Fin l) × (Fin l) ↦
    phobic.get a.1 && phobic.get a.2 && nearby go (fold.get a.1) (fold.get a.2) && (
         a.1.1.succ < a.2.1
      ∨ a.2.1.succ < a.1.1
    )
  )
  univ
)
= 2 * card (filter (λ a : (Fin l) × (Fin l) ↦
  (phobic.get a.1 && phobic.get a.2 && nearby go (fold.get a.1) (fold.get a.2))  ∧ a.1.1.succ < a.2.1) univ)
  := by
  let Q := twice_fold (λ i j : Fin l ↦ phobic.get i && phobic.get j && nearby go (fold.get i) (fold.get j)) hP
  simp
  simp at Q
  exact Q

theorem twice_fold_pts' {α:Type} {β : Type} [Fintype β] (go : β → α → α) [DecidableEq α]
 {l : ℕ} (fold : Vector α l) (phobic : Vector Bool l)
(hP: Symmetric (λ i j : Fin l ↦ phobic.get i && phobic.get j && nearby go (fold.get i) (fold.get j))):
-- should use symmetric_nearby_helper₀ here
card (filter (
    λ a : (Fin l) × (Fin l) ↦
    phobic.get a.1 && phobic.get a.2 && nearby go (fold.get a.1) (fold.get a.2) && (
         a.1.1.succ < a.2.1
      ∨ a.2.1.succ < a.1.1
    )
) univ) = 2 * points_tot go phobic fold
  := by
  rw [twice_fold_pts go fold phobic hP];simp;unfold points_tot pt_loc;congr;simp
  apply funext;intro ik;simp;constructor;norm_num;intro h₁ h₂ h₃ h₄;tauto;tauto
-- 3/14/2024.

def handshake_map_3_to_2  {α:Type} {b:ℕ}
  -- map (i,j) to ((i,a),j) and then drop the j. iaj = ((i,a),j)
  (go : Fin b → α → α) [DecidableEq α]
  {l : ℕ} (fold : Vector α l.succ)
  (phobic : Vector Bool l.succ) :
  filter (
    λ iaj : ((Fin l.succ) × (Fin b)) × (Fin l.succ) ↦
      phobic.get iaj.1.1 && phobic.get iaj.2
      && (fold.get iaj.2) = go iaj.1.2 (fold.get iaj.1.1)
      && (iaj.1.1.1.succ < iaj.2.1 ∨ iaj.2.1.succ < iaj.1.1.1)
  ) univ
  →  filter (
    λ ia : ((Fin l.succ) × (Fin b)) ↦ -- ia = (i,a)
    ∃ j : Fin l.succ, phobic.get ia.1 && phobic.get j
      && (fold.get j) = go ia.2 (fold.get ia.1)
      && (ia.1.1.succ < j.1 ∨ j.1.succ < ia.1.1)
  ) univ
:= λ iaj ↦ ⟨iaj.1.1,by simp;exists iaj.1.2;let Q := iaj.2;simp at Q;tauto⟩



def handshake_map_2_to_3  {α:Type} {b:ℕ}
  -- map (i,j) to ((i,a),j) and then drop the j.
  (go : Fin b → α → α) [DecidableEq α]
  {l : ℕ} (fold : Vector α l.succ)
  (phobic : Vector Bool l.succ)
  :
    filter (
    λ ij : (Fin l.succ) × (Fin l.succ) ↦
    phobic.get ij.1 && phobic.get ij.2 && nearby go (fold.get ij.1) (fold.get ij.2)
      && (ij.1.1.succ < ij.2.1 ∨ ij.2.1.succ < ij.1.1)
  ) univ →
  filter (
    λ iaj : ((Fin l.succ) × (Fin b)) × (Fin l.succ) ↦ -- ia = (i,a)
      phobic.get iaj.1.1 && phobic.get iaj.2
      && ((fold.get iaj.2) = go iaj.1.2 (fold.get iaj.1.1))
      && (iaj.1.1.1.succ < iaj.2.1 ∨ iaj.2.1.succ < iaj.1.1.1)
  ) univ
:= λ ij ↦ by
  simp at ij
  let Q := ij.2.1.2
  unfold nearby at Q
  simp at Q
  let a' := Fin.find (λ a ↦ fold.get ij.1.2 = go a (fold.get ij.1.1))
  have ha': Option.isSome a' := Fin.isSome_find_iff.mpr Q
  let a := a'.get ha'
  let i := ij.1.1
  let j := ij.1.2
  exact ⟨(⟨i,a⟩,j),by
    simp
    constructor;constructor;constructor
    . exact ij.2.1.1.1
    . exact ij.2.1.1.2
    unfold nearby
    simp
    exact Fin.find_spec
          (λ a : Fin b ↦ fold.get ij.1.2 = go a (fold.get ij.1.1))
          (Option.get_mem ha')
    exact ij.2.2
  ⟩

theorem handshake_2_to_3_injective
  {α:Type} {b:ℕ}
  -- let's just map (i,j) to (i,j,a) and then drop the j.
  (go : Fin b → α → α) [DecidableEq α]
  {l : ℕ} (fold : Vector α l.succ)
  (phobic : Vector Bool l.succ):
  Function.Injective (handshake_map_2_to_3 go fold phobic) := by
    intro ⟨i₁,j₁⟩ ⟨i₂,j₂⟩ h
    unfold handshake_map_2_to_3 at h
    simp at h
    have : i₁ = i₂ := by apply Prod.ext; tauto;tauto
    exact SetCoe.ext this

theorem handshake_3_to_2_injective
  {α:Type} {b:ℕ}
  -- let's just map (i,j) to (i,j,a) and then drop the j.
  (go : Fin b → α → α) [DecidableEq α]
  {l : ℕ} (fold : Vector α l.succ)
  (hfold : Function.Injective (λ i ↦ fold.get i))
  (phobic : Vector Bool l.succ):
  Function.Injective (handshake_map_3_to_2 go fold phobic) := by
  intro iajp₁ iajp₂ h
  unfold handshake_map_3_to_2 at h
  simp at h
  let p₁ := iajp₁.2;simp at p₁
  let p₂ := iajp₂.2;simp at p₂
  let j₁ := iajp₁.1.2
  let j₂ := iajp₂.1.2
  apply SetCoe.ext; apply Prod.ext
  tauto; apply hfold
  show fold.get j₁ = fold.get j₂
  rw [p₁.1.2, p₂.1.2, h]

def handshake_map_2_to_2  {α:Type} {b:ℕ}
  -- map (i,j) to ((i,a),j) and then drop the j.
  (go : Fin b → α → α) [DecidableEq α]
  {l : ℕ} (fold : Vector α l.succ)
  (phobic : Vector Bool l.succ)
  :
    filter (
    λ ij : (Fin l.succ) × (Fin l.succ) ↦
    phobic.get ij.1 && phobic.get ij.2 && nearby go (fold.get ij.1) (fold.get ij.2)
      && (ij.1.1.succ < ij.2.1 ∨ ij.2.1.succ < ij.1.1)
  ) univ
  →  filter (
    λ ia : ((Fin l.succ) × (Fin b)) ↦ -- ia = (i,a)
    ∃ j : Fin l.succ, phobic.get ia.1 && phobic.get j
      && (fold.get j) = go ia.2 (fold.get ia.1)
      && (ia.1.1.succ < j.1 ∨ j.1.succ < ia.1.1)
  ) univ
:= λ ij ↦ handshake_map_3_to_2 go fold phobic (handshake_map_2_to_3 go fold phobic ij)

theorem handshake_map_2_to_2_injective  {α:Type} {b:ℕ}
  -- map (i,j) to (i,a) injectively. 3/16/2024
  (go : Fin b → α → α) [DecidableEq α]
  {l : ℕ} (fold : Vector α l.succ)
  (phobic : Vector Bool l.succ)
  (hfold : Function.Injective (λ i ↦ fold.get i))
  : Function.Injective (handshake_map_2_to_2 go fold phobic) := by
    intro ij₁ ij₂ h
    unfold handshake_map_2_to_2 at h

    apply handshake_3_to_2_injective at h
    apply handshake_2_to_3_injective at h
    exact h
    exact hfold


theorem handshake_card₀
  {α:Type} {b:ℕ}
  -- map (i,j) to ((i,a),j) and then drop the j.
  (go : Fin b → α → α) [DecidableEq α]
  {l : ℕ} (fold : Vector α l.succ)
  (phobic : Vector Bool l.succ)
  (hfold : Function.Injective (λ i ↦ fold.get i))
  : card (
    filter (
    λ ij : (Fin l.succ) × (Fin l.succ) ↦
    phobic.get ij.1 && phobic.get ij.2 && nearby go (fold.get ij.1) (fold.get ij.2)
      && (ij.1.1.succ < ij.2.1 ∨ ij.2.1.succ < ij.1.1)
  ) univ)
  ≤ card ( filter (
    λ ia : ((Fin l.succ) × (Fin b)) ↦ -- ia = (i,a)
    ∃ j : Fin l.succ, phobic.get ia.1 && phobic.get j
      && (fold.get j) = go ia.2 (fold.get ia.1)
      && (ia.1.1.succ < j.1 ∨ j.1.succ < ia.1.1)
  ) univ)
:= by
  let α' := filter (
    λ ij : (Fin l.succ) × (Fin l.succ) ↦
    phobic.get ij.1 && phobic.get ij.2 && nearby go (fold.get ij.1) (fold.get ij.2)
      && (ij.1.1.succ < ij.2.1 ∨ ij.2.1.succ < ij.1.1)
  ) univ
  let β' := filter (
    λ ia : ((Fin l.succ) × (Fin b)) ↦ -- ia = (i,a)
    ∃ j : Fin l.succ, phobic.get ia.1 && phobic.get j
      && (fold.get j) = go ia.2 (fold.get ia.1)
      && (ia.1.1.succ < j.1 ∨ j.1.succ < ia.1.1)
  ) univ
  let f : α' → β'
    :=  λ a ↦ (handshake_map_2_to_2 go fold phobic a)
  let s : Finset α' := univ
  let t : Finset β' := univ

  have hf : ∀ a ∈ s, f a ∈ t := by
    intro a;intro;simp
  have f_inj : ∀ a₁ ∈ s, ∀ a₂ ∈ s, f a₁ = f a₂ → a₁ = a₂ := by
    intro a₁
    intro
    intro a₂
    intro
    intro hf
    apply handshake_map_2_to_2_injective
    exact hfold
    exact hf
  have : s.card ≤ t.card := Finset.card_le_card_of_inj_on f hf f_inj
  simp at this
  simp
  tauto


theorem handshake_card₁
  {α:Type} {b:ℕ}
  -- map (i,j) to ((i,a),j) and then drop the j.
  (go : Fin b → α → α) [DecidableEq α]
  {l : ℕ} (fold : Vector α l.succ)
  (phobic : Vector Bool l.succ)
  (hfold : Function.Injective (λ i ↦ fold.get i))
  (hP: Symmetric (λ i j : Fin l.succ ↦ phobic.get i && phobic.get j && nearby go (fold.get i) (fold.get j)))
  : points_tot go phobic fold ≤ l.succ * b / 2
:= by
  suffices 2 * points_tot go phobic fold ≤ l.succ * b by
    refine Nat.le_div_two_iff_mul_two_le.mpr ?_
    suffices  (points_tot go phobic fold) * 2 ≤ (Nat.succ l * b) by
      exact Int.toNat_le.mp this
    rw [Nat.mul_comm] at this
    tauto
  let U := (Finset.univ : Finset (Fin l.succ × Fin b))
  calc
  2 * points_tot go phobic fold = card (filter (
    λ a : (Fin l.succ) × (Fin l.succ) ↦
    phobic.get a.1 && phobic.get a.2 && nearby go (fold.get a.1) (fold.get a.2)
      && (a.1.1.succ < a.2.1 ∨ a.2.1.succ < a.1.1)
    ) univ) := (twice_fold_pts' go fold phobic hP).symm
  _ ≤ card ( filter (
    λ ia : (Fin l.succ) × (Fin b) ↦ -- ia = (i,a)
    ∃ j : Fin l.succ, phobic.get ia.1 && phobic.get j
      && (fold.get j) = go ia.2 (fold.get ia.1)
      && (ia.1.1.succ < j.1 ∨ j.1.succ < ia.1.1)
    ) univ) := handshake_card₀ _ _ _ hfold
  _ ≤ card ( filter (λ _ ↦ True) U) := Finset.card_le_card (by intro x; intro;simp)
  _ = card U := by
    refine (card_eq_of_equiv ?i).symm
    simp
    rfl
  _ = l.succ * b := by
    rw [Finset.card_univ]
    simp

-- #check (univ: Finset (Fin 2)) ×ˢ (univ: Finset (Fin 2))
-- #check (Fin 2) × (Fin 2)
-- #check (univ: Finset (Fin 2)) × (univ: Finset (Fin 2))
theorem cartesian_prod {x y : ℕ} {P: Fin x → Prop} {Q: Fin y → Prop}
  [DecidablePred fun a => P a]
  [DecidablePred fun a => Q a]
  :  (filter (λ ab : Fin x                ×                 Fin y ↦ P ab.1 ∧ Q ab.2) univ)
  =  (filter (λ a : (Fin x)  ↦ P a) univ) ×ˢ (filter (λ b : Fin y  ↦ Q b) univ)
  := by refine ext ?_;intro ab;simp

theorem cartesian_prod' {x y : ℕ} {P: Fin x → Prop}
  [DecidablePred fun a => P a]
  :  (filter (λ ab : Fin x                ×                 Fin y ↦ P ab.1) univ)
  =  (filter (λ a : (Fin x)  ↦ P a) univ) ×ˢ (univ : Finset (Fin y))
  := by refine ext ?_;intro ab;simp

theorem card_product_set_type {x y : ℕ} {P: Fin x → Prop} {Q: Fin y → Prop}
  [DecidablePred fun a => P a]
  [DecidablePred fun a => Q a]
  : card (filter (λ ab : (Fin x) × (Fin y) ↦ P ab.1 ∧ Q ab.2) univ)
  = card (filter (λ a : (Fin x)  ↦ P a) univ)
  * card (filter (λ b : (Fin y)  ↦ Q b) univ)
  := by rw [cartesian_prod,card_product]

theorem card_product_set_type' (x y : ℕ) (P: Fin x → Prop)
  [DecidablePred fun a => P a]
  : card (filter (λ ab : (Fin x) × (Fin y) ↦ P ab.1) univ)
  = card (filter (λ a : (Fin x)  ↦ P a) univ) * y
  := by rw [cartesian_prod',card_product];simp

-- need a "P ab.1 ∧ Q ab" version of card_product_set_type:
theorem card_product_set_type'' (x y : ℕ) (P: Fin x → Prop)
  (Q: Fin x × Fin y → Prop)
  [DecidablePred fun a => P a]
  [DecidablePred fun a => Q a]
  : card (filter (λ ab : (Fin x) × (Fin y) ↦ P ab.1 ∧ Q ab) univ)
  ≤ card (filter (λ a : (Fin x)  ↦ P a) univ)
  * y
  := by calc
    _ ≤ card (filter (λ ab : (Fin x) × (Fin y) ↦ P ab.1) univ) := by
      apply card_le_card;intro ab h;simp at *;tauto
    _ = _ := card_product_set_type' _ _ _

/- To strengthen handshake_card₁
we can also bound in terms of mumtrue, using card_product_set_type'
-/
def numtrue {l:ℕ} : Vector Bool l → ℕ := λ v ↦
  card (filter (λ i ↦ v.get i = true) (univ : Finset (Fin l)))

theorem symmetric_nearby_helper₀
 {α: Type} [DecidableEq α] {b:ℕ}
{go: Fin b → α → α}
{l:ℕ} (ph : Vector Bool l.succ)
(fold : Vector α l.succ)
(hP: Symmetric (λ x y ↦ nearby go x y)):
Symmetric (λ i j : Fin l.succ ↦ ph.get i && ph.get j && nearby go (fold.get i) (fold.get j))
:= by
  intro x y h;simp;simp at h;constructor;constructor;tauto;tauto;rw [hP];simp;tauto

theorem handshake_card₂
  {α:Type} {b:ℕ}
  -- Like Lemma 2.1 in Agarwala et al. 3/17/2024
  (go : Fin b → α → α) [DecidableEq α]
  {l : ℕ} (fold : Vector α l.succ)
  (phobic : Vector Bool l.succ)
  (hfold : Function.Injective (λ i ↦ fold.get i))
  (h_P: Symmetric (λ x y ↦ nearby go x y))
  : points_tot go phobic fold ≤ (numtrue phobic) * b / 2
:= by
  have hP: Symmetric (λ i j : Fin l.succ ↦ phobic.get i && phobic.get j && nearby go (fold.get i) (fold.get j))
    := symmetric_nearby_helper₀ _ _ h_P

  suffices 2 * points_tot go phobic fold ≤ (numtrue phobic) * b by
    refine Nat.le_div_two_iff_mul_two_le.mpr ?_
    suffices  (points_tot go phobic fold) * 2 ≤ ((numtrue phobic) * b) by
      exact Int.toNat_le.mp this
    rw [Nat.mul_comm] at this
    tauto
  calc
  2 * points_tot go phobic fold = card (filter (
    λ a : (Fin l.succ) × (Fin l.succ) ↦
    phobic.get a.1 && phobic.get a.2 && nearby go (fold.get a.1) (fold.get a.2)
      && (a.1.1.succ < a.2.1 ∨ a.2.1.succ < a.1.1)
    ) univ)                                         := (twice_fold_pts' go fold phobic hP).symm
  _ ≤ card ( filter (
    λ ia : (Fin l.succ) × (Fin b) ↦ -- ia = (i,a)
    ∃ j : Fin l.succ, phobic.get ia.1 && phobic.get j && (fold.get j) = go ia.2 (fold.get ia.1)
      && (ia.1.1.succ < j.1 ∨ j.1.succ < ia.1.1)
    ) univ)                                         := handshake_card₀ _ _ _ hfold
  _ = card ( filter (
    λ ia : (Fin l.succ) × (Fin b) ↦ -- ia = (i,a)
    phobic.get ia.1 && (∃ j : Fin l.succ, phobic.get j && (fold.get j) = go ia.2 (fold.get ia.1)
      && (ia.1.1.succ < j.1 ∨ j.1.succ < ia.1.1))
    ) univ) := by
      congr;simp;apply funext;intro ab;simp;constructor;intro h;constructor;tauto;obtain ⟨j,hj⟩ := h
      exists j;tauto;intro h;obtain ⟨j,hj⟩ := h.2;exists j;tauto
  _ ≤ _                         := by simp; exact card_product_set_type'' l.succ b (λ i ↦ phobic.get i) _

theorem symmetric_nearby_helper
 {α: Type} [OfNat α 0] [DecidableEq α] {b:ℕ}
{go: Fin b → α → α}
{l:ℕ} (ph : Vector Bool l.succ)
(moves: Vector (Fin b) l)
(hP: Symmetric (λ x y ↦ nearby go x y)):
Symmetric (λ i j : Fin l.succ ↦ ph.get i && ph.get j && nearby go ((pathᵥ go moves).get i) ((pathᵥ go moves).get j))
:= symmetric_nearby_helper₀ _ _ hP

theorem symmetric_pts_earned_bound_dir' {α: Type} [OfNat α 0] [DecidableEq α] {b:ℕ}
{go: Fin b → α → α}
{l:ℕ} (ph : Vector Bool l.succ)
(moves: Vector (Fin b) l)
(path_inj  : (Function.Injective fun k => Vector.get (pathᵥ go moves) k))
(hP: Symmetric (λ x y ↦ nearby go x y)) -- don't need right_injective left_injective go
: points_tot go ph (pathᵥ go moves) ≤ l.succ * b / 2 := by
  exact handshake_card₁ go (pathᵥ go moves) ph path_inj (symmetric_nearby_helper _  _ hP)
