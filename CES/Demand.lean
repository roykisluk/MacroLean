import Mathlib

/-!
# CES demand: a worked example of the MacroLean workflow

A textbook CES consumer: goods `j ∈ S`, prices `p j > 0`, income `y`, elasticity of
substitution `σ ≠ 1`.

What is checked:
* the price index `P = (Σ_j p_j^{1-σ})^{1/(1-σ)}` is positive;
* expenditure shares are `ω_j = p_j^{1-σ} / Σ_k p_k^{1-σ}` and sum to one;
* spending on good `j` is `ω_j y`, so demand exhausts the budget;
* indirect utility is `y / P` (needs `σ ≠ 0` as well).

Not checked:
* that this demand maximizes utility on the budget set (needs Hölder's inequality);
* the Cobb–Douglas limit `σ → 1`.
-/

open Finset Real

noncomputable section

namespace CES

variable {K : Type*}

/-- `P^{1-σ} = Σ_{j∈S} p_j^{1-σ}`. -/
def sumPow (σ : ℝ) (S : Finset K) (p : K → ℝ) : ℝ := ∑ j ∈ S, p j ^ (1 - σ)

/-- Price index `P = (Σ_{j∈S} p_j^{1-σ})^{1/(1-σ)}`. -/
def P (σ : ℝ) (S : Finset K) (p : K → ℝ) : ℝ := sumPow σ S p ^ (1 - σ)⁻¹

/-- Demand `C_j = (p_j / P)^{-σ} · y / P`. -/
def demand (σ : ℝ) (S : Finset K) (p : K → ℝ) (y : ℝ) (j : K) : ℝ :=
  (p j / P σ S p) ^ (-σ) * (y / P σ S p)

/-- Expenditure share `ω_j = (p_j / P)^{1-σ}`. -/
def share (σ : ℝ) (S : Finset K) (p : K → ℝ) (j : K) : ℝ := (p j / P σ S p) ^ (1 - σ)

/-- Utility `U = (Σ_{j∈S} C_j^{(σ-1)/σ})^{σ/(σ-1)}`. -/
def U (σ : ℝ) (S : Finset K) (C : K → ℝ) : ℝ :=
  (∑ j ∈ S, C j ^ ((σ - 1) / σ)) ^ (σ / (σ - 1))

variable {σ y : ℝ} {S : Finset K} {p : K → ℝ}

lemma sumPow_pos (hS : S.Nonempty) (hp : ∀ j, 0 < p j) : 0 < sumPow σ S p :=
  Finset.sum_pos (fun j _ => rpow_pos_of_pos (hp j) _) hS

lemma P_pos (hS : S.Nonempty) (hp : ∀ j, 0 < p j) : 0 < P σ S p :=
  rpow_pos_of_pos (sumPow_pos hS hp) _

lemma P_rpow (hσ : σ ≠ 1) (hS : S.Nonempty) (hp : ∀ j, 0 < p j) :
    P σ S p ^ (1 - σ) = sumPow σ S p :=
  rpow_inv_rpow (sumPow_pos hS hp).le (sub_ne_zero.2 (Ne.symm hσ))

lemma share_eq (hσ : σ ≠ 1) (hS : S.Nonempty) (hp : ∀ j, 0 < p j) (j : K) :
    share σ S p j = p j ^ (1 - σ) / sumPow σ S p := by
  rw [share, div_rpow (hp j).le (P_pos hS hp).le, P_rpow hσ hS hp]

/-- Shares sum to one. -/
theorem share_sum (hσ : σ ≠ 1) (hS : S.Nonempty) (hp : ∀ j, 0 < p j) :
    ∑ j ∈ S, share σ S p j = 1 := by
  simp_rw [share_eq hσ hS hp, ← Finset.sum_div]
  exact div_self (sumPow_pos hS hp).ne'

/-- Spending on good `j`: `p_j C_j = ω_j y`. -/
theorem expenditure (hS : S.Nonempty) (hp : ∀ j, 0 < p j) (j : K) :
    p j * demand σ S p y j = share σ S p j * y := by
  have hP := P_pos (σ := σ) hS hp
  have hr : 0 < p j / P σ S p := div_pos (hp j) hP
  have : share σ S p j = (p j / P σ S p) * (p j / P σ S p) ^ (-σ) := by
    rw [share, sub_eq_add_neg, rpow_add hr, rpow_one]
  rw [this, demand]
  field_simp

/-- Demand exhausts the budget: `Σ_j p_j C_j = y`. -/
theorem budget (hσ : σ ≠ 1) (hS : S.Nonempty) (hp : ∀ j, 0 < p j) :
    ∑ j ∈ S, p j * demand σ S p y j = y := by
  simp_rw [expenditure hS hp, ← Finset.sum_mul, share_sum hσ hS hp, one_mul]

/-- Indirect utility `U(C) = y / P`. -/
theorem indirect_utility (hσ : σ ≠ 1) (hσ0 : σ ≠ 0) (hy : 0 < y) (hS : S.Nonempty)
    (hp : ∀ j, 0 < p j) : U σ S (demand σ S p y) = y / P σ S p := by
  have hP := P_pos (σ := σ) hS hp
  have hyP : 0 < y / P σ S p := div_pos hy hP
  have hσ1 : σ - 1 ≠ 0 := sub_ne_zero.2 hσ
  have key : ∀ j ∈ S, demand σ S p y j ^ ((σ - 1) / σ)
      = share σ S p j * (y / P σ S p) ^ ((σ - 1) / σ) := by
    intro j _
    have hr : 0 < p j / P σ S p := div_pos (hp j) hP
    rw [demand, mul_rpow (rpow_pos_of_pos hr _).le hyP.le, ← rpow_mul hr.le, share]
    congr 2
    field_simp
    ring
  rw [U, Finset.sum_congr rfl key, ← Finset.sum_mul, share_sum hσ hS hp, one_mul,
    ← rpow_mul hyP.le]
  have : (σ - 1) / σ * (σ / (σ - 1)) = 1 := by field_simp
  rw [this, rpow_one]

end CES
