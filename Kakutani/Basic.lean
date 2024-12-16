import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Sets.Closeds
import Mathlib.Analysis.Convex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Bornology.Basic

-- Definitions
def ConvexCompactNonempty {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E] (K : Set E) :=
  Convex ℝ K ∧ IsCompact K ∧ K.Nonempty

def UpperHemicontinuous {E : Type _} [TopologicalSpace E] (f : E → Set E) :=
  ∀ x₀ : E, ∀ U : Set E, IsOpen U → f x₀ ⊆ U →
    ∃ V : Set E, IsOpen V ∧ x₀ ∈ V ∧ ∀ x ∈ V, f x ⊆ U

def NonemptyConvexCompactValued {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (f : E → Set E) :=
  ∀ x : E, Convex ℝ (f x) ∧ IsCompact (f x) ∧ (f x).Nonempty

-- Lemma: Existence of continuous selection
lemma continuous_selection {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] (K : Set E) (f : E → Set E) :
  ConvexCompactNonempty K →
  UpperHemicontinuous f →
  NonemptyConvexCompactValued f →
  (∀ x ∈ K, f x ⊆ K) →
  ∃ g : E → E, ContinuousOn g K ∧ ∀ x ∈ K, g x ∈ f x :=
by sorry


open Metric Bornology Topology
-- Lemma: No retraction from ball to sphere exists
lemma no_retraction_of_ball_to_sphere {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] :
  ¬ ∃ r : E → E, ContinuousOn r (closedBall (0 : E) 1) ∧
    (∀ x ∈ closedBall (0 : E) 1, r x ∈ sphere (0 : E) 1) ∧
    (∀ x ∈ sphere (0 : E) 1, r x = x) :=
by sorry




-- Brouwer's Fixed Point Theorem
theorem brouwer_fixed_point {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] (K : Set E) (g : E → E) :
  Convex ℝ K → IsCompact K → K.Nonempty →
  ContinuousOn g K →
  (∀ x ∈ K, g x ∈ K) →
  ∃ x ∈ K, g x = x := by

  intro h_convex h_compact h_nonempty h_continuous h_maps_into
  -- Assume for contradiction that g has no fixed point in K
  by_contra! h_no_fixed_point
  -- Define a function f that "pushes" points towards the boundary
  let f : E → E := fun x => x + (1 / ‖g x - x‖) • (g x - x)
  -- Show that f is continuous on K
  have h_f_continuous : ContinuousOn f K := by
    -- Since g is continuous on K, so is g - id
    have h_g_minus_id : ContinuousOn (fun x => g x - x) K :=
      ContinuousOn.sub h_continuous continuousOn_id
    -- The norm is continuous, so ‖g x - x‖ is continuous on K
    have h_norm : ContinuousOn (fun x => ‖g x - x‖) K :=
      ContinuousOn.norm h_g_minus_id
    -- On K, ‖g x - x‖ > 0 since g has no fixed point
    have h_pos : ∀ x ∈ K, ‖g x - x‖ ≠ 0 := by
      intro x hx
      rw [norm_ne_zero_iff, sub_ne_zero]
      exact h_no_fixed_point x hx
    -- Thus, 1 / ‖g x - x‖ is continuous on K
    have h_inv_norm : ContinuousOn (fun x => 1 / ‖g x - x‖) K := by
      have duh : (fun x =>  1 / ‖g x - x‖) = (fun x => ‖g x - x‖⁻¹) := by
        funext
        rw [inv_eq_one_div]
      rw [duh]
      exact sorry
    -- Scalar multiplication is continuous on K
    have h_smul : ContinuousOn (fun x => (1 / ‖g x - x‖) • (g x - x)) K :=
      ContinuousOn.smul h_inv_norm h_g_minus_id
    -- Addition is continuous, so f is continuous on K
    exact ContinuousOn.add continuousOn_id h_smul

  -- Show that f maps K into the boundary of K
  have h_f_maps_to_boundary : ∀ x ∈ K, f x ∈ frontier K := by
    intros x hx
    -- Since K is compact, it is closed and bounded
    have hK_closed : IsClosed K := h_compact.isClosed
    have hK_bounded := h_compact.isBounded

    -- Since K is bounded, there exists M > 0 such that ∀ y ∈ K, ‖y‖ ≤ M

    obtain ⟨M, hM'⟩ := hK_bounded.subset_ball 0
    have hM : ∀ y ∈ K, ‖y‖ < M := by
      intro y hy
      specialize hM' hy
      rw [mem_ball_zero_iff] at hM'
      exact hM'
    clear hM'
    -- f x = x + (1 / ‖g x - x‖) • (g x - x)
    have h_fx_minus_x_norm : ‖f x - x‖ = 1 := by
      unfold f
      simp only [one_div, add_sub_cancel_left]
      rw [norm_smul, norm_inv, norm_norm]
      field_simp
      sorry

    -- Suppose f x ∈ interior K
    by_contra h_not_frontier
    have h_interior : f x ∈ interior K := by
      rw [frontier_eq_closure_inter_closure] at h_not_frontier
      simp at h_not_frontier
      apply h_not_frontier
      sorry

    -- Then there exists ε > 0 such that ball (f x) ε ⊆ K
    rw [mem_interior] at h_interior
    rcases mem_interior.2 h_interior with ⟨T,hT,hT'⟩
    simp at hT
    rcases hT with ⟨T_open, T_sset⟩


    obtain ⟨ε, hε_pos, h_ball_subset⟩ := Metric.is_open_iff.mp is_open_interior f x h_interior
    -- Consider y = f x + (ε / 2) • (f x - x)
    let y := f x + (ε / 2) • (f x - x)
    -- Compute ‖y - f x‖ = (ε / 2) * ‖f x - x‖ = ε / 2
    have h_dist : dist y f x = ε / 2 := by
      rw [dist_eq_norm, add_sub_cancel, norm_smul, h_fx_minus_x_norm]
      simp
    -- So y ∈ ball (f x) ε
    have h_y_in_ball : y ∈ Metric.ball (f x) ε := by
      rw [Metric.mem_ball, h_dist]
      linarith
    -- Therefore, y ∈ K
    have h_y_in_K : y ∈ K := h_ball_subset h_y_in_ball
    -- Show that ‖y‖ > M, contradicting the boundedness of K
    have h_norm_y : ‖y‖ ≥ ‖f x‖ + (ε / 2) := by
      calc
        ‖y‖ = ‖f x + (ε / 2) • (f x - x)‖ := rfl
        _ ≥ ‖f x‖ + ‖(ε / 2) • (f x - x)‖ - 0 := norm_add_ge_norm_sub _ _
        _ = ‖f x‖ + (ε / 2) * ‖f x - x‖ := by rw [norm_smul, h_fx_minus_x_norm]
        _ = ‖f x‖ + (ε / 2) * 1 := by rw [h_fx_minus_x_norm]
        _ = ‖f x‖ + (ε / 2) := by ring
    -- Since f x = x + (unit vector), ‖f x‖ ≥ ‖x‖ - 1
    have h_norm_fx : ‖f x‖ ≥ ‖x‖ - 1 := by
      calc
        ‖f x‖ = ‖x + (1 / ‖g x - x‖) • (g x - x)‖ := rfl
        _ ≥ ‖x‖ - ‖(1 / ‖g x - x‖) • (g x - x)‖ := norm_sub_norm_le _ _
        _ = ‖x‖ - 1 := by rw [h_fx_minus_x_norm]
    -- Thus, ‖y‖ ≥ ‖x‖ - 1 + (ε / 2)
    have h_norm_y_lower : ‖y‖ ≥ ‖x‖ - 1 + (ε / 2) := by linarith
    -- Since ‖x‖ ≤ M (as x ∈ K), we get ‖y‖ ≥ M - 1 + (ε / 2)
    have h_norm_y_bound : ‖y‖ ≥ M - 1 + (ε / 2) := by
      have h_norm_x_le : ‖x‖ ≤ M := hM hx
      linarith
    -- For ε small enough, this contradicts ‖y‖ ≤ M
    have h_y_not_in_K : ‖y‖ > M := by linarith [h_norm_y_bound]
    -- But y ∈ K implies ‖y‖ ≤ M, contradiction
    exact h_y_not_in_K.not_le (hM h_y_in_K)
  -- Since f x ∈ closure K and not in interior K, f x ∈ frontier K
  conclude f x ∈ frontier K

  -- Extend f to a continuous function on the closed ball
  -- This gives a retraction from the ball to its boundary
  have h_retraction : ∃ r : E → E, ContinuousOn r (closedBall (0 : E) (M + 1)) ∧
    (∀ x ∈ closedBall (0 : E) (M + 1), r x ∈ sphere (0 : E) (M + 1)) ∧
    (∀ x ∈ sphere (0 : E) (M + 1), r x = x) := by
    let φ : E → E := fun x =>
      if h : x = 0 then 0 else (M + 1) • (x / ‖x‖)
    have h_continuous_on : ContinuousOn φ ({0}ᶜ) := by
      apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.div continuousOn_id continuousOn_norm
      intros x hx; simp [hx]
    have h_continuous : ContinuousOn φ (closedBall 0 (M + 1)) := by
      apply ContinuousOn_if
      · exact is_closed_eq continuous_id continuous_const
      · exact continuousOn_const
      · exact h_continuous_on.mono (closure_subset_iff_subset_of_is_closed (is_closed_ball).compl).mpr (subset_univ _)
    use φ
    refine ⟨h_continuous, _, _⟩
    · intros x hx
      by_cases h : x = 0
      · simp [φ, h, norm_zero, (M + 1)]
      · simp [φ, h, norm_smul, norm_div, norm_norm, mul_div_cancel', ne_of_gt (norm_pos_iff.mpr h)]
    · intros x hx
      have : ‖x‖ = M + 1 := by rwa [mem_sphere_iff_norm] at hx
      simp [φ, this]
  -- This contradicts the no retraction lemma
  exact no_retraction_of_ball_to_sphere h_retraction


-- Outline of the proof of Kakutani's Fixed Point Theorem
theorem kakutani_fixed_point {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] (K : Set E) (f : E → Set E) :
  ConvexCompactNonempty K →
  UpperHemicontinuous f →
  NonemptyConvexCompactValued f →
  (∀ x ∈ K, f x ⊆ K) →
  ∃ x ∈ K, x ∈ f x := by
  intro hK h_upper h_valued h_subset
  -- Step 1: Use the continuous selection lemma to get a continuous function g
  have h_exists_g : ∃ g : E → E, ContinuousOn g K ∧ ∀ x ∈ K, g x ∈ f x := continuous_selection K f hK h_upper h_valued h_subset
  rcases h_exists_g with ⟨g, h_g⟩
  -- Step 2: g is continuous on K and maps K into itself
  have h_g_maps_to_K : ∀ x ∈ K, g x ∈ K := fun x hx => h_subset x hx (h_g.right x hx)
  -- Step 3: Apply Brouwer's Fixed Point Theorem to g
  have h_fixed_point : ∃ x ∈ K, g x = x := brouwer_fixed_point K g hK.left hK.right.left hK.right.right h_g.left h_g_maps_to_K
  -- Step 4: This fixed point x satisfies x ∈ f x
  rcases h_fixed_point with ⟨x, hx⟩
  use x
  constructor
  exact hx.left
  . have := h_g.right x hx.left
    rw (config := {occs := .pos [2]}) [←hx.right]
    exact this
