import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Sets.Closeds
import Mathlib.Analysis.Convex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Defs

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


open Metric
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
    have h_g_minus_id : ContinuousOn (fun x => g x - x) K := sorry
    -- The norm is continuous, so ‖g x - x‖ is continuous on K
    have h_norm : ContinuousOn (fun x => ‖g x - x‖) K := ContinuousOn.norm h_g_minus_id
    -- On K, ‖g x - x‖ > 0 since g has no fixed point
    have h_pos : ∀ x ∈ K, ‖g x - x‖ ≠ 0 := by
      intro x hx
      sorry
      -- rw [ne_zero_iff_norm_ne_zero, sub_eq_zero]
      -- exact h_no_fixed_point x hx
    -- Thus, 1 / ‖g x - x‖ is continuous on K
    have h_inv_norm : ContinuousOn (fun x => 1 / ‖g x - x‖) K := sorry
    -- Scalar multiplication is continuous on K
    have h_smul : ContinuousOn (fun x => (1 / ‖g x - x‖) • (g x - x)) K :=
      ContinuousOn.smul h_inv_norm h_g_minus_id
    -- Addition is continuous, so f is continuous on K
    sorry

  -- Show that f maps K into the boundary of K
  have h_f_maps_to_boundary : ∀ x ∈ K, f x ∈ frontier K := sorry
  -- Extend f to a continuous function on the closed ball
  -- This gives a retraction from the ball to its boundary
  have h_retraction : ∃ r : E → E, ContinuousOn r (closedBall (0 : E) 1) ∧
    (∀ x ∈ closedBall (0 : E) 1, r x ∈ sphere (0 : E) 1) ∧
    (∀ x ∈ sphere (0 : E) 1, r x = x) := sorry
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
