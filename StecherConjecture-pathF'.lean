import MyProject.StecherConjecture_SpringBreak2024
import MyProject.StecherConjectureF
set_option tactic.hygienic false

-- pathF' is like pathF but without the infinity
def pathF'  {α β:Type} [OfNat α 0] {l:ℕ} (go : β → α → α)
  (moves : Fin l → β): Fin l.succ → α := by
  induction l
  intro
  exact 0
  intro i
  by_cases h : i.1 < n.succ
  exact                n_ih (λ j ↦ moves (Fin.castSucc j)) ⟨i.1,h⟩
  exact go (moves n)  (n_ih (λ j ↦ moves (Fin.castSucc j)) n)
-- #print pathF'

def morF {l:ℕ} -- 3/10/24
  {α:Type} [OfNat α 0] {b₀ b₁ : ℕ} (f : Fin b₀ → α → Fin b₁.succ)
  (go : Fin b₀ → α → α)
  (moves : Fin l.succ →  (Fin b₀))
  :        Fin l.succ → (Fin b₁.succ) := by
  induction l
  intro i
  have : i = 0 := Fin.eq_zero i
  subst this
  . exact f (moves 0) 0
  intro i
  let R := pathF' go moves ⟨i.1,Nat.lt.step i.2⟩
  exact f (moves i) R

-- rotate_morfF finished 3/10/24. It vindicates some definition changes,
-- although it still wasn't all that easy.
lemma rotate_morfF {l:ℕ} (moves: Fin l.succ → Fin 4) (k : Fin l.succ.succ):
  rotate (pathF' rect                  moves  k) =
         (pathF' rect (morfF rotateIndex moves)) k
  -- if we try this with pathF instead of pathF' then the dif_pos doesn't work
:= by
  induction l
  cases Nat.of_le_succ (Fin.is_le k)

  have : k = 0 := Fin.le_zero_iff.mp h
  subst this
  unfold pathF'
  simp
  . rfl

  have : k = 1 := Fin.ext h
  subst this
  unfold pathF'
  simp
  rw [rotate_basic 0 (moves 0)]
  . rfl

  by_cases h : k.1 < n.succ.succ

  let R := n_ih (λ i ↦ moves (Fin.castSucc i)) ⟨k.1,h⟩
  simp at R
  have : pathF' rect (morfF rotateIndex (λ i ↦ moves (Fin.castSucc i))) ⟨k.1,h⟩
       = pathF' rect (morfF rotateIndex moves )  k := by
        unfold pathF'
        simp
        unfold morfF
        rw [dif_pos h] -- apply? suggested: exact (dif_pos h).symm
  rw [← this]
  rw [← R]
  have : pathF' rect        moves                    k
       = pathF' rect (λ i ↦ moves (Fin.castSucc i)) ⟨k.1,h⟩ := by
    exact dif_pos h -- vindicating pathF'
  . rw [this]

  have : k.1 = n.succ.succ := Nat.eq_of_lt_succ_of_not_lt k.2 h
  have : k = ⟨n.succ.succ, Nat.lt.base (Nat.succ (Nat.succ n))⟩
    := Fin.eq_mk_iff_val_eq.mpr this
  subst this

  simp at this
  unfold pathF'
  simp
  repeat (rw [rotate_basic])
  let R₁ := n_ih (λ i ↦ moves (Fin.castSucc i)) ⟨n, Nat.lt.step (Nat.lt.base n)⟩
  unfold pathF' at R₁
  unfold morfF at R₁
  simp at R₁

  let T  := (Nat.rec (motive := fun {l} => (Fin l → Fin 4) → Fin (Nat.succ l) → ℤ × ℤ)
      (fun _ _ => 0)
      (fun n n_ih moves i =>
        if h : i.1 < Nat.succ n then
          n_ih (fun j => moves (Fin.castSucc j)) ⟨ i.1,h⟩
        else rect (moves (Fin.last n)) (n_ih (fun j => moves (Fin.castSucc j)) (Fin.last n)))
      n
      (fun j => moves (Fin.castSucc (Fin.castSucc j))) -- difference S,T
      (Fin.last n)) -- difference T, T'
  let T' := (Nat.rec (motive := fun {l} => (Fin l → Fin 4) → Fin (Nat.succ l) → ℤ × ℤ)
      (fun _ _ => 0)
      (fun n n_ih moves i =>
        if h : ↑i < Nat.succ n then
          n_ih (fun j => moves (Fin.castSucc j)) ⟨i.1,h⟩
        else rect (moves (Fin.last n)) (n_ih (fun j => moves (Fin.castSucc j)) (Fin.last n)))
      n
      (fun j => moves (Fin.castSucc (Fin.castSucc j)))
      ⟨n,Nat.lt.base n⟩) -- difference T, T'

  let S := (Nat.rec (motive := fun {l} => (Fin l → Fin 4) → Fin (Nat.succ l) → ℤ × ℤ)
      (fun _ _ => 0)
      (fun n n_ih moves i =>
        if h : i.1 < Nat.succ n then
          n_ih (fun j => moves (Fin.castSucc j)) ⟨i.1,h⟩
        else rect (moves (Fin.last n)) (n_ih (fun j => moves (Fin.castSucc j)) (Fin.last n)))
      n
      (fun j => rotateIndex (moves (Fin.castSucc (Fin.castSucc j)))) -- difference S,T
      (Fin.last n))
  let S' := Nat.rec (motive := fun {l} => (Fin l → Fin 4) → Fin (Nat.succ l) → ℤ × ℤ)
    (fun _ _ => 0)
    (fun n n_ih moves i =>
      if h : ↑i < Nat.succ n then
        n_ih (fun j => moves (Fin.castSucc j)) ⟨i.1,h⟩
      else rect (moves (Fin.last n)) (n_ih (fun j => moves (Fin.castSucc j)) (Fin.last n)))
    n (fun j => rotateIndex (moves (Fin.castSucc (Fin.castSucc j))))
    ⟨n,Nat.lt.base n⟩

  have hT: T = T' := rfl
  have hS: S = S' := rfl
  have : (rotate T) = S := by
    rw [hT,hS]
    exact R₁
  rw [this]
  rfl

lemma reflect_morfF {l:ℕ} (moves: Fin l.succ → Fin 4) (k : Fin l.succ.succ):
  reflect (pathF' rect                  moves  k) =
         (pathF' rect (morfF reflectIndex moves)) k
:= by
  induction l
  cases Nat.of_le_succ (Fin.is_le k)

  have : k = 0 := Fin.le_zero_iff.mp h
  subst this
  unfold pathF'
  simp
  . rfl

  have : k = 1 := Fin.ext h
  subst this
  unfold pathF'
  simp
  rw [reflect_basic 0 (moves 0)]
  . rfl

  by_cases h : k.1 < n.succ.succ

  let R := n_ih (λ i ↦ moves (Fin.castSucc i)) ⟨k.1,h⟩
  simp at R
  have : pathF' rect (morfF reflectIndex (λ i ↦ moves (Fin.castSucc i))) ⟨k.1,h⟩
       = pathF' rect (morfF reflectIndex moves )  k := by
        unfold pathF'
        simp
        unfold morfF
        rw [dif_pos h] -- apply? suggested: exact (dif_pos h).symm
  rw [← this]
  rw [← R]
  have : pathF' rect        moves                    k
       = pathF' rect (λ i ↦ moves (Fin.castSucc i)) ⟨k.1,h⟩ := by
    exact dif_pos h -- vindicating pathF'
  . rw [this]

  have : k.1 = n.succ.succ := Nat.eq_of_lt_succ_of_not_lt k.2 h
  have : k = ⟨n.succ.succ, Nat.lt.base (Nat.succ (Nat.succ n))⟩
    := Fin.eq_mk_iff_val_eq.mpr this
  subst this

  simp at this
  unfold pathF'
  simp
  repeat (rw [reflect_basic])
  let R₁ := n_ih (λ i ↦ moves (Fin.castSucc i)) ⟨n, Nat.lt.step (Nat.lt.base n)⟩

  unfold pathF' at R₁
  unfold morfF at R₁
  simp at R₁

  let T  := (Nat.rec (motive := fun {l} => (Fin l → Fin 4) → Fin (Nat.succ l) → ℤ × ℤ)
      (fun _ _ => 0)
      (fun n n_ih moves i =>
        if h : i.1 < Nat.succ n then
          n_ih (fun j => moves (Fin.castSucc j)) ⟨ i.1,h⟩
        else rect (moves (Fin.last n)) (n_ih (fun j => moves (Fin.castSucc j)) (Fin.last n)))
      n
      (fun j => moves (Fin.castSucc (Fin.castSucc j))) -- difference S,T
      (Fin.last n)) -- difference T, T'
  let T' := (Nat.rec (motive := fun {l} => (Fin l → Fin 4) → Fin (Nat.succ l) → ℤ × ℤ)
      (fun _ _ => 0)
      (fun n n_ih moves i =>
        if h : ↑i < Nat.succ n then
          n_ih (fun j => moves (Fin.castSucc j)) ⟨i.1,h⟩
        else rect (moves (Fin.last n)) (n_ih (fun j => moves (Fin.castSucc j)) (Fin.last n)))
      n
      (fun j => moves (Fin.castSucc (Fin.castSucc j)))
      ⟨n,Nat.lt.base n⟩) -- difference T, T'

  let S := (Nat.rec (motive := fun {l} => (Fin l → Fin 4) → Fin (Nat.succ l) → ℤ × ℤ)
      (fun _ _ => 0)
      (fun n n_ih moves i =>
        if h : i.1 < Nat.succ n then
          n_ih (fun j => moves (Fin.castSucc j)) ⟨i.1,h⟩
        else rect (moves (Fin.last n)) (n_ih (fun j => moves (Fin.castSucc j)) (Fin.last n)))
      n
      (fun j => reflectIndex (moves (Fin.castSucc (Fin.castSucc j)))) -- difference S,T
      (Fin.last n))
  let S' := Nat.rec (motive := fun {l} => (Fin l → Fin 4) → Fin (Nat.succ l) → ℤ × ℤ)
    (fun _ _ => 0)
    (fun n n_ih moves i =>
      if h : ↑i < Nat.succ n then
        n_ih (fun j => moves (Fin.castSucc j)) ⟨i.1,h⟩
      else rect (moves (Fin.last n)) (n_ih (fun j => moves (Fin.castSucc j)) (Fin.last n)))
    n (fun j => reflectIndex (moves (Fin.castSucc (Fin.castSucc j))))
    ⟨n,Nat.lt.base n⟩

  have hT: T = T' := rfl
  have hS: S = S' := rfl
  have : (reflect T) = S := by
    rw [hT,hS]
    exact R₁
  rw [this]
  rfl

theorem rotate_preserves_pt_loc'F {l:ℕ}
-- completed 3/10/24 at the cost of adding ".succ" to l
  (moves : Fin l.succ → (Fin 4)) (i j : Fin l.succ.succ) (ph: Fin l.succ.succ → Bool)
  (hpt: pt_locF κ (pathF' rect             moves)  i j ph)
  :     pt_locF κ (pathF' rect (morfF rotateIndex moves)) i j ph
  := by
    unfold pt_locF at *
    simp at *
    constructor
    . tauto
    let R := rotate_preserves_nearby ((pathF' rect moves) i)
                                     ((pathF' rect moves) j) hpt.2

    rw [rotate_morfF moves i, rotate_morfF moves j] at R
    . tauto

theorem reflect_preserves_pt_loc'_morfF {l:ℕ}
  (moves : Fin l.succ → (Fin 4)) (i j : Fin l.succ.succ) (ph: Fin l.succ.succ → Bool)
  (hpt: pt_locF κ (pathF' κ             moves)  i j ph)
  :     pt_locF κ (pathF' κ (morfF reflectIndex moves)) i j ph
  := by
    unfold pt_locF at *
    simp at *
    constructor
    . tauto
    let R := reflect_preserves_nearby ((pathF' κ moves) i)
                                     ((pathF' κ moves) j) hpt.2
    rw [reflect_morfF moves i, reflect_morfF moves j] at R
    tauto

theorem rotate_pts'_atF {l:ℕ} (k : Fin l.succ.succ)
  (ph    : Fin l.succ.succ → Bool)
  (moves : Fin l.succ → (Fin 4)):
  pts_at'F κ k ph (pathF' κ moves) ≤
  pts_at'F κ k ph (pathF' κ (morfF rotateIndex moves)) := by
  -- Completed March 10, 2024. The point of using pathF' and morfF here is to be able to combine
  -- with the work on "orderly".
  apply Finset.card_le_card
  intro i hi
  let Q :=  rotate_preserves_pt_loc'F moves i k ph
  simp at *
  tauto

theorem reflect_pts'_atF {l:ℕ} (k : Fin l.succ.succ)
  (ph    : Fin l.succ.succ → Bool)
  (moves : Fin l.succ → (Fin 4)):
  -- 3/10/24
  pts_at'F κ k ph (pathF' κ moves) ≤
  pts_at'F κ k ph (pathF' κ (morfF reflectIndex moves)) := by
  apply Finset.card_le_card
  intro i hi
  let Q :=  reflect_preserves_pt_loc'_morfF moves i k ph
  simp at *
  tauto

theorem rotate_pts_totF
  -- 3/10/24. Combine with "orderly" work
  {l:ℕ} (ph : Fin l.succ.succ → Bool) (moves : Fin l.succ → (Fin 4)):
  pts_tot'F κ ph (pathF' κ moves) ≤
  pts_tot'F κ ph (pathF' κ (morfF rotateIndex moves))
  := by
    unfold pts_tot'F
    apply Finset.sum_le_sum
    intro k
    intro
    exact rotate_pts'_atF k ph moves

theorem reflect_pts_tot_morfF
  {l:ℕ} (ph : Fin l.succ.succ → Bool) (moves : Fin l.succ → (Fin 4)):
  pts_tot'F κ ph (pathF' κ moves) ≤
  pts_tot'F κ ph (pathF' κ (morfF reflectIndex moves))
  -- 3/8/24
  := by
    unfold pts_tot'F
    apply Finset.sum_le_sum
    intro k
    intro
    exact reflect_pts'_atF k ph moves

theorem towards_orderlyishF
  -- 3/10/24. Note some "simp" uses are unnecessary when using pathF', morfF
  {l:ℕ} (ph : Fin l.succ.succ → Bool)(moves : Fin l.succ → (Fin 4)):
  ∃ moves' : Fin l.succ → (Fin 4), moves' 0 = 0 ∧
  pts_tot'F κ ph (pathF' κ moves) ≤
  pts_tot'F κ ph (pathF' κ moves')
  := by
  cases can_be_orderlyish (moves 0)
  exists moves
  cases h
  exists (morfF rotateIndex moves)
  constructor
  rw [← h_1]
  symm
  simp at h_1
  exact rotate_headF _

  exact rotate_pts_totF ph moves
  cases h_1
  exists (morfF rotateIndex (morfF rotateIndex moves))
  constructor
  rw [← h]
  let Q₀ := rotate_headF moves
  let Q₁ := rotate_headF (morfF rotateIndex moves)
  rw [Q₀,Q₁]
  calc
    pts_tot'F κ ph (pathF' κ moves) ≤ pts_tot'F κ ph (pathF' κ (morfF rotateIndex (moves))):= rotate_pts_totF ph moves
    _ ≤ _ := rotate_pts_totF ph (morfF rotateIndex (moves))

  let m₀ := moves
  let m₁ := (morfF rotateIndex m₀)
  let m₂ := (morfF rotateIndex m₁)
  let m₃ := (morfF rotateIndex m₂)
  exists m₃
  constructor
  rw [← h]
  simp
  . rw [rotate_headF m₀,rotate_headF m₁,rotate_headF m₂]

  calc
    pts_tot'F κ ph (pathF' κ m₀) ≤ pts_tot'F κ ph (pathF' κ m₁) := rotate_pts_totF ph m₀
    _                      ≤ pts_tot'F κ ph (pathF' κ m₂) := rotate_pts_totF ph m₁
    _                      ≤ _                      := rotate_pts_totF ph m₂

theorem towards_orderlyF
  {l:ℕ} (ph : Fin l.succ.succ → Bool)(moves : Fin l.succ → (Fin 4)):
  ∃ moves', moves' 0 = 0 ∧
  (∀ j, (∀ i, i < j → moves' i = 0 ∨ moves' i = 1) → moves' j ≠ 3) ∧
  pts_tot'F κ ph (pathF' κ moves) ≤
  pts_tot'F κ ph (pathF' κ moves')
  -- completed 3/10/24.
  := by
  obtain ⟨moves₀,hmoves₀⟩ := towards_orderlyishF ph moves
  by_cases h₃: (∀ j, (∀ i, i < j → moves₀ i = 0 ∨ moves₀ i = 1) → moves₀ j ≠ 3)
  exists moves₀
  . tauto
  have : ∃ (j : Fin (l + 1)),
    (∀ i < j, moves₀ i = 0 ∨ moves₀ i = 1) ∧ moves₀ j = 3
    := by
      contrapose h₃;simp;intro x hx;contrapose h₃;simp;simp at h₃;exists x
  obtain ⟨j,hj⟩ := this
  have : (morfF reflectIndex moves₀) j = 2 := by
    let Q := hj.2;unfold morfF reflectIndex;rw [Q];rfl
  exists (morfF reflectIndex moves₀)
  constructor
  let Q := hmoves₀.1;unfold reflectIndex morfF;simp;simp at Q;rw [Q];rfl

  constructor
  intro j₁ hj₁;by_cases h : j₁ < j;let Q := hj.1 j₁ h
  -- now it's easy using morfF
  cases Q
  intro hc;unfold morfF at hc;rw [h_1] at hc;contrapose hc;decide
  intro hc;unfold morfF at hc;rw [h_1] at hc;contrapose hc;decide
  by_cases he : j₁ = j
  subst he;rw [this];symm;decide

  have : j < j₁ ∨ j = j₁ ∨ j₁ < j := lt_trichotomy j j₁
  have : j < j₁ := by tauto
  let Q := hj.2
  let R := hj₁ j this
  cases R
  unfold morfF at h_1;rw [Q] at h_1;contrapose h_1;decide
  unfold morfF at h_1;rw [Q] at h_1;contrapose h_1;decide
  calc
  _ ≤ pts_tot'F κ ph (pathF' κ moves₀) := hmoves₀.2
  _ ≤ _                          := reflect_pts_tot_morfF ph moves₀
