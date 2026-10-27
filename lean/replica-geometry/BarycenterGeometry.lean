import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Geometry-preserving replicated bands and the barycenter-only obstruction

This file proves finite deterministic geometric and normalization identities.
The final gap certificate is CONDITIONAL on the indicated thermodynamic
inequalities. No Gaussian comparison, Parisi formula, generalized TAP
approximation, Gibbs limit, or large-deviation theorem is claimed here.
-/

open scoped BigOperators
open Finset

namespace BarycenterAudit

/-- A finite Gram-array estimate. Only the upper off-diagonal bound and the
lower mixed-overlap bound are needed. Positive semidefiniteness is unnecessary
for this algebraic lemma; the next theorem supplies actual Gram arrays. -/
theorem gram_error_bound {k : ℕ} (hk : 0 < k)
    (G : Fin k → Fin k → ℝ) (B : Fin k → ℝ) (q δ : ℝ)
    (hδ : 0 ≤ δ) (hdiag : ∀ i, G i i = 1)
    (hoff : ∀ i j, i ≠ j → G i j ≤ q + δ)
    (hmixed : ∀ i, q - δ ≤ B i) :
    ((∑ i, ∑ j, G i j) - 2 * (k : ℝ) * (∑ i, B i) + (k : ℝ)^2 * q) /
        (k : ℝ)^2 ≤ (1 - q) / (k : ℝ) + 3 * δ := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hrow (i : Fin k) :
      (∑ j, G i j) ≤ 1 + ((k : ℝ) - 1) * (q + δ) := by
    calc
      (∑ j, G i j) ≤ ∑ j : Fin k, ((q + δ) + if j = i then 1 - q - δ else 0) := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hji : j = i
        · subst j
          simp [hdiag]
        · simp only [hji, ↓reduceIte, add_zero]
          exact hoff i j (Ne.symm hji)
      _ = 1 + ((k : ℝ) - 1) * (q + δ) := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ,
          ↓reduceIte]
        ring
  have hsum : (∑ i, ∑ j, G i j) ≤ (k : ℝ) * (1 + ((k : ℝ) - 1) * (q + δ)) := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
      (Finset.sum_le_sum (s := Finset.univ) (fun (i : Fin k) _ => hrow i))
  have hmix : (k : ℝ) * (q - δ) ≤ ∑ i, B i := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
      (Finset.sum_le_sum (s := Finset.univ) (fun (i : Fin k) _ => hmixed i))
  have hmix2 := mul_le_mul_of_nonneg_left hmix (show (0 : ℝ) ≤ 2 * k by positivity)
  have hδk : 0 ≤ δ * (k : ℝ) := mul_nonneg hδ hkR.le
  apply (div_le_iff₀ (pow_pos hkR 2)).2
  have heq : ((1 - q) / (k : ℝ) + 3 * δ) * (k : ℝ)^2 =
      (1 - q) * (k : ℝ) + 3 * δ * (k : ℝ)^2 := by
    field_simp
  rw [heq]
  nlinarith

/-- The exact squared-distance identity, before imposing any overlap bounds. -/
theorem barycenter_square_identity
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {k : ℕ} (hk : 0 < k) (σ : Fin k → E) (m : E)
    {N : ℝ} (hN : 0 < N) :
    ‖((k : ℝ)⁻¹) • (∑ i, σ i) - m‖^2 / N =
      ((∑ i, ∑ j, inner ℝ (σ i) (σ j) / N) -
        2 * (k : ℝ) * (∑ i, inner ℝ (σ i) m / N) +
        (k : ℝ)^2 * (‖m‖^2 / N)) / (k : ℝ)^2 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hnorm : ‖((k : ℝ)⁻¹) • (∑ i, σ i)‖^2 =
      ((k : ℝ)⁻¹)^2 * (∑ i, ∑ j, inner ℝ (σ i) (σ j)) := by
    rw [← real_inner_self_eq_norm_sq, real_inner_smul_left, real_inner_smul_right, sum_inner]
    simp_rw [inner_sum]
    ring
  rw [norm_sub_sq_real, hnorm, real_inner_smul_left, sum_inner]
  simp only [← Finset.sum_div]
  field_simp

/-- Preserving the replicated-band geometry forces the empirical barycenter
to be close to its target, uniformly in the ambient real inner-product space. -/
theorem geometry_preserving_barycenter_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {k : ℕ} (hk : 0 < k) (σ : Fin k → E) (m : E)
    {N δ : ℝ} (hN : 0 < N) (hδ : 0 ≤ δ)
    (hspin : ∀ i, ‖σ i‖^2 = N)
    (hmixed : ∀ i, |inner ℝ (σ i) m / N - ‖m‖^2 / N| ≤ δ)
    (hoff : ∀ i j, i ≠ j →
      |inner ℝ (σ i) (σ j) / N - ‖m‖^2 / N| ≤ δ) :
    ‖((k : ℝ)⁻¹) • (∑ i, σ i) - m‖^2 / N ≤
      (1 - ‖m‖^2 / N) / (k : ℝ) + 3 * δ := by
  rw [barycenter_square_identity hk σ m hN]
  apply gram_error_bound hk _ _ _ δ hδ
  · intro i
    rw [real_inner_self_eq_norm_sq, hspin]
    exact div_self (ne_of_gt hN)
  · intro i j hij
    have h := le_of_abs_le (hoff i j hij)
    linarith
  · intro i
    have h := neg_le_of_abs_le (hmixed i)
    linarith

/-- A slightly weaker version, independent of the target self-overlap. -/
theorem geometry_preserving_barycenter_bound_simple
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {k : ℕ} (hk : 0 < k) (σ : Fin k → E) (m : E)
    {N δ : ℝ} (hN : 0 < N) (hδ : 0 ≤ δ)
    (hspin : ∀ i, ‖σ i‖^2 = N)
    (hmixed : ∀ i, |inner ℝ (σ i) m / N - ‖m‖^2 / N| ≤ δ)
    (hoff : ∀ i j, i ≠ j →
      |inner ℝ (σ i) (σ j) / N - ‖m‖^2 / N| ≤ δ) :
    ‖((k : ℝ)⁻¹) • (∑ i, σ i) - m‖^2 / N ≤ 1 / (k : ℝ) + 3 * δ := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have h := geometry_preserving_barycenter_bound hk σ m hN hδ hspin hmixed hoff
  have hq : 0 ≤ ‖m‖^2 / N := by positivity
  have hdiv : (1 - ‖m‖^2 / N) / (k : ℝ) ≤ 1 / (k : ℝ) :=
    div_le_div_of_nonneg_right (by linarith) hkR.le
  linarith

/-- Exact partition-weight normalization. W is the constrained replicated
weight and Z is the unnormalized one-replica partition sum. The expression
for U removes k H(m) and N k log 2, exactly as in the manuscript. -/
theorem constrained_cost_identity {N W Z H : ℝ} {k : ℕ}
    (hN : 0 < N) (hk : 0 < k) (hW : 0 < W) (hZ : 0 < Z) :
    -Real.log (W / Z^k) / (N * (k : ℝ)) =
      (Real.log Z - N * Real.log 2) / N - H / N -
        (Real.log W - (k : ℝ) * H - N * (k : ℝ) * Real.log 2) /
          (N * (k : ℝ)) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  rw [Real.log_div (ne_of_gt hW) (pow_ne_zero _ (ne_of_gt hZ)), Real.log_pow]
  field_simp
  ring

/-- The equivalent exponential normalization formula. This is an identity
of positive partition weights; it contains no asymptotic TAP assumption. -/
theorem constrained_probability_identity {N W Z H : ℝ} {k : ℕ}
    (hN : 0 < N) (hk : 0 < k) (hW : 0 < W) (hZ : 0 < Z) :
    W / Z^k = Real.exp (N * (k : ℝ) *
      (H / N +
        (Real.log W - (k : ℝ) * H - N * (k : ℝ) * Real.log 2) /
          (N * (k : ℝ)) -
        (Real.log Z - N * Real.log 2) / N)) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hlog : Real.log (W / Z^k) = N * (k : ℝ) *
      (H / N +
        (Real.log W - (k : ℝ) * H - N * (k : ℝ) * Real.log 2) /
          (N * (k : ℝ)) -
        (Real.log Z - N * Real.log 2) / N) := by
    rw [Real.log_div (ne_of_gt hW) (pow_ne_zero _ (ne_of_gt hZ)), Real.log_pow]
    field_simp
    ring
  rw [← hlog, Real.exp_log (div_pos hW (pow_pos hZ _))]

/-- General obstruction: the thermodynamic inputs are explicit hypotheses.
The result holds under the weaker algebraic assumption t<=1, without
needing beta>=0 or t>=0. -/
theorem general_rate_gap {f C R β c a t L : ℝ}
    (ht : t ≤ 1) (hf : β * c - L ≤ f) (hC : C ≤ β * a)
    (hR : R ≤ t * (f + L)) :
    β * ((1 - t) * c - a) - L ≤ f - C - R := by
  have h := mul_le_mul_of_nonneg_left hf (sub_nonneg.mpr ht)
  nlinarith

theorem log_two_bounds : 0 < Real.log 2 ∧ Real.log 2 < 7 / 10 := by
  constructor
  · exact Real.log_pos (by norm_num)
  · have h := Real.log_two_lt_d9
    linarith

/-- Exact rational certificate for the deliberately coarse SK constants. -/
theorem explicit_rate_gap_bound {f C R : ℝ}
    (hf : 4000 - Real.log 2 ≤ f) (hC : C ≤ 352 / 125)
    (hR : R ≤ (999 / 1000 : ℝ) * (f + Real.log 2)) :
    148 / 125 - Real.log 2 ≤ f - C - R := by
  linarith

/-- A strict gap larger than 0.484, not a certification of the assumed
spin-glass estimates. The logarithm inequality is proved in mathlib. -/
theorem explicit_rate_gap {f C R : ℝ}
    (hf : 4000 - Real.log 2 ≤ f) (hC : C ≤ 352 / 125)
    (hR : R ≤ (999 / 1000 : ℝ) * (f + Real.log 2)) :
    121 / 250 < f - C - R := by
  have h := explicit_rate_gap_bound hf hC hR
  have hlog := log_two_bounds.2
  linarith

theorem proposed_rate_ne_actual {f C R : ℝ}
    (hf : 4000 - Real.log 2 ≤ f) (hC : C ≤ 352 / 125)
    (hR : R ≤ (999 / 1000 : ℝ) * (f + Real.log 2)) : f - C ≠ R := by
  have h := explicit_rate_gap hf hC hR
  linarith

end BarycenterAudit

#print axioms BarycenterAudit.gram_error_bound
#print axioms BarycenterAudit.barycenter_square_identity
#print axioms BarycenterAudit.geometry_preserving_barycenter_bound
#print axioms BarycenterAudit.geometry_preserving_barycenter_bound_simple
#print axioms BarycenterAudit.constrained_cost_identity
#print axioms BarycenterAudit.constrained_probability_identity
#print axioms BarycenterAudit.general_rate_gap
#print axioms BarycenterAudit.log_two_bounds
#print axioms BarycenterAudit.explicit_rate_gap_bound
#print axioms BarycenterAudit.explicit_rate_gap
#print axioms BarycenterAudit.proposed_rate_ne_actual
