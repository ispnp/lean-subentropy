module

public import SubentropyCertificates.MaximalCoupling
public import SubentropyCertificates.ClassicalTableGuessing
public import SubentropyCertificates.CurveTangent

/-! Classical part of Theorem 13. The modulus and spectral extremizers are due
to Hanson and Datta. This proof uses the manuscript's maximal-coupling argument. -/
@[expose] public section
noncomputable section
open Set Filter
open scoped BigOperators Topology

namespace SubentropyCertificates.Continuity
open SubentropyCertificates.ClassicalCurve

variable {X : Type*} [Fintype X] [DecidableEq X]

def modulus (m : ℕ) (δ : ℝ) : ℝ := phi m (min δ (uniformError m))

/-- A maximal coupling turns the subentropy difference into two conditional
subentropies of the same joint law. Either orientation has the same guessing error. -/
theorem classical_continuity_bound (m : ℕ) (hn : Fintype.card X = m + 2)
    (p q : X → ℝ) (hp : p ∈ probabilitySimplex X) (hq : q ∈ probabilitySimplex X) :
    |classicalSubentropy p - classicalSubentropy q| ≤ modulus m (totalVariation p q) := by
  obtain ⟨J, hJ, hr, hc, hdiag, he⟩ := exists_maximal_coupling p q hp hq
  let w := fun u : X × X ↦ J u.1 u.2
  have fwd := classical_joint_guessing m hn p q hp J hJ hr hc
  have rev := classical_joint_guessing m hn q p hq (fun i j ↦ J j i) (fun i j ↦ hJ j i) hc hr
  have swap := classical_subentropy_reindex w (Equiv.prodComm X X)
  change classicalSubentropy (fun u : X × X ↦ J u.2 u.1) = classicalSubentropy w at swap
  change 0 ≤ classicalSubentropy w - classicalSubentropy q ∧
    classicalSubentropy w - classicalSubentropy q ≤ _ at fwd
  dsimp only at rev
  rw [swap] at rev
  rw [he] at fwd rev
  have hab : |classicalSubentropy p - classicalSubentropy q| ≤ phi m (totalVariation p q) :=
    abs_le.mpr ⟨by linarith [rev.2, fwd.1], by linarith [fwd.2, rev.1]⟩
  by_cases h : totalVariation p q ≤ uniformError m
  · simpa [modulus, min_eq_left h] using hab
  · have ht : totalVariation p q ∈ Icc 0 1 := by
      refine ⟨div_nonneg (Finset.sum_nonneg (fun i _ ↦ abs_nonneg _)) (by norm_num), ?_⟩
      rw [← he]
      linarith [Finset.sum_nonneg (s := Finset.univ) (fun i _ ↦ hJ i i)]
    simpa [modulus, min_eq_right (le_of_not_ge h)] using hab.trans (phi_le_uniform_max m ht)

/-- Distance between the explicit extremizer and the point mass at its distinguished label. -/
theorem extremal_totalVariation (m : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    totalVariation (extremalVector m u) (extremalVector m 0) = u := by
  have hd : (0 : ℝ) < (m + 1 : ℕ) := by positivity
  simp only [totalVariation, Fintype.sum_option, extremalVector, sub_zero, zero_div,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [show 1 - u - 1 = -u by ring, abs_neg, abs_of_nonneg hu,
    abs_of_nonneg (div_nonneg hu hd.le)]
  field_simp
  ring

/-- At every allowed radius the point mass and the extremal vector attain the
modulus. Their actual distance stops at the uniform endpoint. -/
theorem classical_modulus_attained (m : ℕ) (hn : Fintype.card X = m + 2)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    ∃ p q : X → ℝ, p ∈ probabilitySimplex X ∧ q ∈ probabilitySimplex X ∧
      totalVariation p q = min δ (uniformError m) ∧
      |classicalSubentropy p - classicalSubentropy q| = modulus m δ := by
  let u := min δ (uniformError m)
  have hu : u ∈ Icc (0 : ℝ) 1 :=
    ⟨le_min hδ (uniformError_mem m).1, (min_le_right ..).trans (uniformError_mem m).2⟩
  let e : X ≃ Option (Fin (m + 1)) := Fintype.equivOfCardEq (by simp [hn, Nat.add_assoc])
  let p := extremalVector m u
  let q := extremalVector m 0
  refine ⟨p ∘ e, q ∘ e, simplex_reindex p (extremal_probability m hu) e,
    simplex_reindex q (extremal_probability m (by constructor <;> norm_num)) e, ?_, ?_⟩
  · change (∑ i, |p (e i) - q (e i)|) / 2 = u
    rw [e.sum_comp (fun i ↦ |p i - q i|)]
    exact extremal_totalVariation m hu.1
  · rw [classical_subentropy_reindex, classical_subentropy_reindex]
    change |phi m u - phi m 0| = phi m u
    have hm := (phi_strictMono m).monotoneOn
      (show (0 : ℝ) ∈ Icc 0 (uniformError m) from ⟨le_rfl, (uniformError_mem m).1⟩)
      (show u ∈ Icc 0 (uniformError m) from ⟨hu.1, min_le_right ..⟩) hu.1
    rw [phi_zero] at hm ⊢
    simp [abs_of_nonneg hm]

/-- The least upper bound is a maximum, including at zero radius and on the plateau. -/
theorem classical_modulus_isGreatest (m : ℕ) (hn : Fintype.card X = m + 2)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    IsGreatest {v : ℝ | ∃ p q : X → ℝ, p ∈ probabilitySimplex X ∧ q ∈ probabilitySimplex X ∧
      totalVariation p q ≤ δ ∧ v = |classicalSubentropy p - classicalSubentropy q|} (modulus m δ) := by
  obtain ⟨p, q, hp, hq, he, hv⟩ := classical_modulus_attained m hn hδ
  refine ⟨⟨p, q, hp, hq, he.le.trans (min_le_left ..), hv.symm⟩, ?_⟩
  rintro v ⟨a, b, ha, hb, hab, rfl⟩
  have ht : 0 ≤ totalVariation a b :=
    div_nonneg (Finset.sum_nonneg fun i _ ↦ abs_nonneg _) (by norm_num)
  apply (classical_continuity_bound m hn a b ha hb).trans
  exact (phi_strictMono m).monotoneOn
    ⟨le_min ht (uniformError_mem m).1, min_le_right ..⟩
    ⟨le_min hδ (uniformError_mem m).1, min_le_right ..⟩ (min_le_min_right _ hab)

private theorem uniform_endpoint_pos (m : ℕ) : 0 < uniformError m := by
  have hn : (1 : ℝ) < (m + 2 : ℕ) := by norm_cast; omega
  exact sub_pos.mpr ((div_lt_one (by positivity)).mpr hn)

/-- Every positive radius has a strictly smaller modulus, including on the plateau. -/
theorem modulus_lt_radius (m : ℕ) {δ : ℝ} (hδ : 0 < δ) : modulus m δ < δ :=
  (phi_lt_error m (lt_min hδ (uniform_endpoint_pos m))
    ((min_le_right ..).trans (uniformError_mem m).2)).trans_le (min_le_left ..)

/-- The ratio to the radius tends to one in every fixed alphabet of size at least two. -/
theorem modulus_div_radius_tendsto_one (m : ℕ) :
    Tendsto (fun δ ↦ modulus m δ / δ) (𝓝[>] 0) (𝓝 1) := by
  apply (phi_div_error_tendsto_one m).congr'
  filter_upwards [Ioo_mem_nhdsGT_of_mem
    (show (0 : ℝ) ∈ Ico 0 (uniformError m) from ⟨le_rfl, uniform_endpoint_pos m⟩)] with δ hδ
  simp [modulus, min_eq_left hδ.2.le]

end SubentropyCertificates.Continuity
