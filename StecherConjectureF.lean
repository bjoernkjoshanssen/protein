import MyProject.StecherConjecture_SpringBreak2024

open BigOperators

set_option tactic.hygienic false

def pt_locF {α:Type} {β : Type} [Fintype β] (go : β → α → α) [DecidableEq α]
 {l : ℕ} (fold : Fin l → α) (i j : Fin l) (phobic : Fin l → Bool) : Bool
:=  phobic i && phobic j && i.1.succ < j.1 && nearby go (fold i) (fold j)

def pts_at'F {α:Type} {β : Type} [Fintype β] (go : β → α → α)
  [DecidableEq α] {l:ℕ} (k : Fin l) (ph : Fin l → Bool) (fold : Fin l → α) : ℕ :=
  Finset.card (
    Finset.filter (λ i : Fin l ↦ (pt_locF go fold i k ph))
    Finset.univ
  )

def change_typeF  {α:Type} {β : Type} [Fintype β] (go : β → α → α)
[DecidableEq α] {l:ℕ} (k : Fin l) (ph : Fin l → Bool) (fold : Fin l → α):
Finset.filter (λ i : Fin l ↦ (pt_locF go fold i k ph)) Finset.univ
→
Finset.filter (λ i : Fin k ↦ (pt_locF go fold ⟨i.1,finfin i⟩ k ph)) Finset.univ
  := by
    intro ip; let Q := ip.2; rw [Finset.mem_filter] at Q -- Finset.mem_filter was key here
    unfold pt_locF at Q;
    have : ip.1.1.succ < k := by
      simp at Q;tauto
    exact ⟨⟨ip.1.1,Nat.lt_of_succ_lt this⟩,by rw [Finset.mem_filter];simp;tauto⟩

theorem change_type_cardF  {α:Type} {β : Type} [Fintype β] (go : β → α → α)
  [DecidableEq α] {l:ℕ} (k : Fin l) (ph : Fin l → Bool) (fold : Fin l → α):
Fintype.card (Finset.filter (λ i : Fin l ↦ (pt_locF go fold i k ph)) Finset.univ)
=
Fintype.card (Finset.filter (λ i : Fin k ↦ (pt_locF go fold ⟨i.1,finfin i⟩ k ph)) Finset.univ)
:= by
  suffices Function.Bijective (change_typeF go k ph fold) by
    apply Fintype.card_of_bijective; exact this
  constructor
  intro i₁ i₂ hi; unfold change_typeF at hi; simp at hi
  exact SetCoe.ext (Fin.ext hi)
  intro i; let Q := i.2; rw [Finset.mem_filter] at Q
  exists ⟨
    ⟨i.1,finfin i.1⟩,
    by rw [Finset.mem_filter]; constructor; simp; exact Q.2
  ⟩

theorem pt_loc_of_embedsF
 {α:Type} [DecidableEq α] {b₀ b₁ : ℕ}
{go₀ : Fin b₀ → α → α} {go₁ : Fin b₁ → α → α} (h_embed : embeds_in go₀ go₁)
 {l:ℕ}
  (fold : Fin l → α) (a b : Fin l) (phobic : Fin l → Bool)
  (htri: pt_locF go₀ fold a b phobic) :
         pt_locF go₁ fold a b phobic := by
  unfold pt_locF at *; simp at *; constructor; tauto; exact nearby_of_embeds h_embed htri.2

theorem pts_at_of_embeds'F {α:Type} [DecidableEq α] {b₀ b₁ : ℕ}
{go₀ : Fin b₀ → α → α} {go₁ : Fin b₁ → α → α} (h_embed : embeds_in go₀ go₁)
{l:ℕ} (k:Fin l) (ph : Fin l → Bool) (fold : Fin l → α):
pts_at'F go₀ k ph fold ≤
pts_at'F go₁ k ph fold := by
  unfold pts_at'F; apply Finset.card_le_card; intro a ha; simp; simp at ha
  exact pt_loc_of_embedsF h_embed fold a k ph ha

def pts_tot'F {α:Type} {β : Type} [Fintype β] (go : β → α → α) [DecidableEq α]
 {l:ℕ} (ph : Fin l → Bool)(fold : Fin l → α)
  := ∑ i : Fin l, pts_at'F go i ph fold

theorem pts_bound_of_embeds'F {α:Type} [DecidableEq α] {b₀ b₁ : ℕ}
{go₀ : Fin b₀ → α → α} {go₁ : Fin b₁ → α → α} (h_embed : embeds_in go₀ go₁)
{l:ℕ} (ph : Fin l → Bool) (fold : Fin l → α):
pts_tot'F go₀ ph fold ≤
pts_tot'F go₁ ph fold := by
  unfold pts_tot'F; apply Finset.sum_le_sum; intros; exact pts_at_of_embeds'F h_embed _ _ _

def pts_atF {α:Type} {β : Type} [Fintype β] (go : β → α → α)
[DecidableEq α] {l:ℕ} (k : Fin l) (ph : Fin l → Bool) (fold : Fin l → α) : ℕ :=
  Finset.card (
    Finset.filter (λ i : Fin k ↦ (pt_locF go fold ⟨i.1,finfin i⟩ k ph))
    Finset.univ
  )

theorem pts_at_eq_pts_at'F  {α:Type} {β : Type} [Fintype β] (go : β → α → α)
[DecidableEq α] {l:ℕ} (k : Fin l) (ph : Fin l → Bool) (fold : Fin l → α):
pts_atF go k ph fold = pts_at'F go k ph fold := by
unfold pts_atF pts_at'F; (repeat rw [← Fintype.card_coe]);
exact (change_type_cardF go k ph fold).symm

lemma pts_at_bound'F {α:Type} [DecidableEq α]
{β : Type} [Fintype β]
(go : β → α → α)
{l:ℕ} (ph : Fin l → Bool) (fold : Fin l → α) (i:Fin l):
pts_at'F go i ph fold ≤ i := by
  rw [← pts_at_eq_pts_at'F, ← Finset.card_fin i.1];
  apply Finset.card_le_card; apply Finset.filter_subset

theorem pts_earned_bound_loc'F {α:Type} [DecidableEq α] {β : Type} [Fintype β] (go : β → α → α)
{l:ℕ} (ph : Fin l.succ → Bool) (fold : Fin l.succ → α):
pts_tot'F go ph fold ≤ l.succ * l / 2 := by
  suffices pts_tot'F go ph fold ≤ ∑ j : Fin l.succ, j.1 by calc
    _ ≤ ∑ j : Fin l.succ, j.1 := this
    _ = _                     := Fin_sum_range _
  unfold pts_tot'F; apply Finset.sum_le_sum; intro i; intro; exact pts_at_bound'F go ph fold i
