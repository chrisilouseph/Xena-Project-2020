/-
Copyright (c) 2020 Chrisil Ouseph. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chrisil Ouseph
-/

import topology.instances.complex tactic

/-!
# Path-Connectedness

This file defines path-connectedness for pairs of points of a topological space, path components
as well as path-connected subsets of a space and path-connected spaces. We build an interface for
these definitions and prove basic related theorems, including pointwise path-connectedness is an
equivalence relation and path-connectedness implies connectedness but not vice-versa (deleted comb
space). We also show some side-lemmas like connectedness of a dense subset implies that of the
entire set, continuity on restricted domains and an alternate characterisation of connectedness.

## Important definitions and classes

* `are_path_connected` : path-connectedness of pairs of points
* `is_pre_path_connected`, `is_path_connected` : path-connected sets (the latter being non-empty)
* `pre_path_connected_space`, `path_connected_space` : path-connected spaces (similar to previous)
* `path_component` : path_components of a space

## Implementation notes

Path-connectedness for sets and points has been implemented as `Prop`, while path-connected spaces
have been defined as classes.

## References

* J. R. Munkres : *Topology* :
https://www.pearson.com/us/higher-education/product/Munkres-Topology-2nd-Edition/9780131816299.html
* K. Conrad : *Spaces that are Connected but not Path-Connected* :
https://kconrad.math.uconn.edu/blurbs/topology/connnotpathconn.pdf

The theorem `continuous_on_if` uses a lemma proved under `continuous_if` in *topology\basic.lean*.
The interface for path-connectedness as well as several of the other proofs have been inspired from
*topology\subset_properties.lean*.
-/

open set
variables {α : Type*} {β : Type*}
variables [topological_space α] [topological_space β]
variables {A B : set α}
variables a b c : A
local notation `I01` := Icc (0 : ℝ) 1

/-- If a dense subset is preconnected, then so is the entire set -/
theorem is_preconnected.dense_subset (hAB : A ⊆ B) (hBcA : B ⊆ closure A)
  (hA : is_preconnected A) : is_preconnected B :=
λ C D hCo hDo hcov ⟨p, hpB, hpC⟩ ⟨q, hqB, hqD⟩,
let ⟨x, hxC, hxA⟩ := mem_closure_iff.mp (hBcA hpB) C hCo hpC in
let ⟨y, hyC, hyD⟩ := mem_closure_iff.mp (hBcA hqB) D hDo hqD in
let ⟨w, hwA, hwCD⟩ := hA C D hCo hDo (trans hAB hcov) ⟨x, hxA, hxC⟩ ⟨y, hyD, hyC⟩ in
⟨w, hAB hwA, hwCD⟩

/-- Continuity on restricted domains -/
theorem continuous_on_if {D : set α} {p : α → Prop} {f g : α → β}
  {h : ∀ a, decidable (p a)} (hp : ∀ a ∈ frontier {a | p a} ∩ D, f a = g a)
  (hf : continuous_on f $ closure {x | p x} ∩ D) (hg : continuous_on g $ closure {x | ¬p x} ∩ D) :
  continuous_on (λ a, @ite (p a) (h a) β (f a) (g a)) D :=
begin
  rw continuous_on_iff_is_closed,
  intros s hs,
  obtain ⟨sf, hsfc, hsf⟩ := (continuous_on_iff_is_closed.mp hf) s hs,
  obtain ⟨sg, hsgc, hsg⟩ := (continuous_on_iff_is_closed.mp hg) s hs,
  refine ⟨sf ∩ closure {a : α | p a} ∪ sg ∩ closure {a : α | ¬p a}, _, _⟩,
  { simp only [is_closed_closure, is_closed_union, is_closed_inter, *]  },
  suffices heq : (λ a, ite (p a) (f a) (g a)) ⁻¹' s ∩ D =
    ((f ⁻¹' s ∩ closure {a | p a}) ∪ (g ⁻¹' s ∩ closure {a | ¬ p a})) ∩ D,
  { rw [heq, union_inter_distrib_right, union_inter_distrib_right],
    assoc_rw [hsf, hsg] },
  ext a,
  classical,
  by_cases hf : a ∈ frontier {a | p a} ∩ D,
  { have hac := hf.left.left,
    have hai : a ∈ closure {a | ¬ p a} := (@closure_compl _ _ p).symm ▸ mem_compl hf.left.right,
    by_cases hpa : p a;
    { simp [hpa, hp a hf, hac, hai, iff_def];
      exact and.intro }},
  rw [inter_comm, inter_comm _ D],
  refine and_congr_right (λ had, _),
  replace hf := not_and'.mp hf had,
  by_cases hpa : p a,
  { have hc : a ∈ closure {a | p a} := subset_closure hpa,
    have hnc : a ∉ closure {a | ¬ p a},
    { show a ∉ closure {a | p a}ᶜ,
      simpa [closure_compl, frontier, hc] using hf  },
    simp [hpa, hc, hnc] },
  have hc : a ∈ closure {a | ¬ p a} := subset_closure hpa,
  have hnc : a ∉ closure {a | p a},
  { change a ∈ closure {a | p a}ᶜ at hc,
    simp [closure_compl] at hc,
    simpa [frontier, hc] using hf },
  simp [hpa, hc, hnc],
end

/-- Two points in a set `A` are path-connected if there exists a path in `A` between them. -/
def are_path_connected (a b : A) :=
  ∃ f : ℝ → α, (∀ x ≤ 0, f x = a) ∧ (∀ x, 1 ≤ x → f x = b) ∧ range f ⊆ A ∧ continuous f

theorem are_path_connected.refl : are_path_connected a a :=
⟨(λ _, a), (λ _ _, rfl), (λ _ _, rfl), (λ _ ⟨_, hx⟩, hx ▸ a.2), continuous_const⟩

theorem are_path_connected.symm : are_path_connected a b → are_path_connected b a :=
λ ⟨f, h0, h1, hr, hc⟩,
⟨λ x, f (1-x),
λ _ _, h1 _ (by linarith),
λ _ _, h0 _ (by linarith),
λ y ⟨x, hy⟩, hr ⟨1-x, hy⟩,
continuous.comp hc $ continuous.sub continuous_const continuous_id⟩

theorem are_path_connected.trans :
  are_path_connected a b → are_path_connected b c → are_path_connected a c :=
begin
  rintro ⟨f, hf0, hf1, hfr, hfc⟩ ⟨g, hg0, hg1, hgr, hgc⟩,
  refine ⟨λ x, ite (x ≤ 1/2) (f (2*x)) (g (2*x - 1)), λ x hx, _, λ x hx, _, _, _⟩,
      { rw ←hf0 (2*x) (by linarith),
        exact if_pos (by linarith)  },
    { rw ←hg1 (2*x-1) (by linarith),
      exact if_neg (by linarith)  },
  { rintro y ⟨x, rfl⟩,
    by_cases h0 : x ≤ 1/2,
      exact hfr ⟨2*x, (if_pos h0).symm⟩,
    exact hgr ⟨2*x - 1, (if_neg h0).symm⟩ },
  refine continuous_if (λ x hx, _) _ _,
    { have h : x = 1/2 := (frontier_le_subset_eq continuous_id continuous_const) hx,
      norm_num [h, hg0, hf1]  },
  { exact continuous.comp hfc (continuous.mul continuous_const continuous_id) },
  refine continuous.comp hgc (continuous.add _ continuous_const),
  exact continuous.mul continuous_const continuous_id,
end

instance : is_equiv A are_path_connected :=
{refl:= are_path_connected.refl, trans:= are_path_connected.trans, symm:= are_path_connected.symm}

theorem are_path_connected.mono {a b : A} {B} (hAB : A ⊆ B) :
  are_path_connected a b → are_path_connected ⟨a.1, hAB a.2⟩ ⟨b.1, hAB b.2⟩ :=
λ ⟨p, hp0, hp1, hpr, hpc⟩, ⟨p, hp0, hp1, trans hpr hAB, hpc⟩

/-- A weaker characterisation of `are_path_connected` for ease of proving concrete examples -/
theorem are_path_connected_iff {a b : A} : are_path_connected a b ↔
  ∃ f : ℝ → α, f 0 = a ∧ f 1 = b ∧ f '' I01 ⊆ A ∧ continuous_on f I01 :=
begin
  split; rintro ⟨p, h0, h1, hr, hc⟩,
  { use [p, h0 0 (le_refl 0), h1 1 (le_refl 1),
      trans (image_subset_range _ _) hr, continuous.continuous_on hc] },

  refine ⟨λ x, ite (x ≤ 0) a (ite (x ≥ 1) b (p x)),λ _ hx, if_pos hx,
    λ _ hx, trans (if_neg (by linarith)) (if_pos hx), _, _⟩,
  { rintro y ⟨x, rfl⟩,
    by_cases hx0 : x ≤ 0,
      {convert a.2,
      exact if_pos hx0},
    by_cases hx1 : x ≥ 1,
      {convert b.2,
      exact trans (if_neg hx0) (if_pos hx1)},
    refine hr ⟨x, _, symm $ trans (if_neg hx0) (if_neg hx1)⟩,
    exact Ioo_subset_Icc_self ⟨lt_of_not_ge hx0, lt_of_not_ge hx1⟩  },
  rw continuous_iff_continuous_on_univ,
  refine continuous_on_if (λ x hx, _) continuous_on_const _,
  { have : x = 0 := (frontier_le_subset_eq continuous_id continuous_const) hx.left,
    rw [this, if_neg (not_le_of_gt zero_lt_one), h0]  },
  refine continuous_on_if (λ x hx, _) continuous_on_const _,
  { have : 1 = x := (frontier_le_subset_eq continuous_const continuous_id) hx.left, cc  },
  push_neg,
  show continuous_on p (closure (Iio 1) ∩ (closure (Ioi 0) ∩ univ)),
  rwa [inter_univ, closure_Iio, closure_Ioi, inter_comm],
end

/-- A set is pre-path-connected if each pair of points in it is path-connected. -/
def is_pre_path_connected (A : set α) := ∀ a b, @are_path_connected _ _ A a b

theorem is_pre_path_connected_empty : is_pre_path_connected (∅ : set α) := λ x, x.2.elim

theorem is_pre_path_connected_sUnion (x : α) {c : set (set α)} (H1 : ∀ s ∈ c, x ∈ s)
  (H2 : ∀ s ∈ c, is_pre_path_connected s) : is_pre_path_connected (⋃₀ c) :=
have H : ∀ y ∈ ⋃₀ c, ∃ t ⊆ ⋃₀ c, x ∈ t ∧ y ∈ t ∧ is_pre_path_connected t,
  from λ y ⟨s, hs, hy⟩, ⟨s, subset_sUnion_of_mem hs, H1 s hs, hy, H2 s hs⟩,
λ a b,
let ⟨sa, hsa, hxsa, hasa, hsap⟩ := H a a.2 in
let ⟨sb, hsb, hxsb, hbsb, hsbp⟩ := H b b.2 in
let hxa := are_path_connected.mono hsa (hsap ⟨x, hxsa⟩ ⟨a, hasa⟩) in
let hxb := are_path_connected.mono hsb (hsbp ⟨x, hxsb⟩ ⟨b, hbsb⟩) in
trans (symm hxa) hxb

theorem is_pre_path_connected_Union {γ : Type*} (x : α) {p : γ → set α} (hx : ∀ g, x ∈ p g)
  (hp : ∀ g, is_pre_path_connected (p g)) : is_pre_path_connected (⋃ i, p i) :=
λ ⟨a, ha⟩ ⟨b, hb⟩,
let ⟨ga, hga⟩ := mem_Union.mp ha in
let ⟨gb, hgb⟩ := mem_Union.mp hb in
trans (are_path_connected.mono (subset_Union _ _) (hp ga ⟨a, hga⟩ ⟨x, hx ga⟩))
  (are_path_connected.mono (subset_Union _ _) (hp gb ⟨x, hx gb⟩ ⟨b, hgb⟩))

theorem is_pre_path_connected.union (x : α) {s t : set α} (hxs : x ∈ s) (hxt : x ∈ t)
  (hs : is_pre_path_connected s) (ht : is_pre_path_connected t) : is_pre_path_connected (s ∪ t) :=
sUnion_pair s t ▸ is_pre_path_connected_sUnion x
  (by rintro r (rfl | rfl | h); assumption)
  (by rintro r (rfl | rfl | h); assumption)

theorem is_pre_path_connected.image {s : set α} (H : is_pre_path_connected s) (f : α → β)
  (hf : continuous_on f s) : is_pre_path_connected (f '' s) :=
λ ⟨fx, x, hx, hfx⟩ ⟨fy, y, hy, hfy⟩,
let ⟨p, hp0, hp1, hpr, hpc⟩ := H ⟨x, hx⟩ ⟨y, hy⟩ in
let hpi := (trans (image_subset_range p I01) hpr) in
are_path_connected_iff.mpr
  ⟨λ x, f (p x),
  by simp [hp0 0 (le_refl 0), hfx],
  by simp [hp1 1 (le_refl 1), hfy],
  symm (image_comp f p I01) ▸ image_subset f hpi,
  continuous_on.comp hf (continuous.continuous_on hpc) (image_subset_iff.mp hpi)⟩

theorem is_pre_path_connected.is_pre_connected (h : is_pre_path_connected A) : is_preconnected A :=
begin
  have hw := @is_preconnected_univ ℝ _ _,
  dsimp [is_preconnected] at hw ⊢,
  contrapose! hw,
  obtain ⟨U, V, hUo, hVo, hcov, ⟨x, ⟨hxa, hxu⟩⟩, ⟨y, ⟨hya, hyu⟩⟩, hi⟩ := hw,
  obtain ⟨f, h0, h1, hr, hc⟩ := h ⟨x, hxa⟩ ⟨y, hya⟩,
  refine ⟨f ⁻¹' U, f ⁻¹' V, hc U hUo, hc V hVo, _, ⟨0, _⟩, ⟨1, _⟩, _⟩,
      { rw ←preimage_union,
        refine trans (trans _ (preimage_mono hr)) (preimage_mono hcov),
        rw preimage_range },
    { rwa [univ_inter, mem_preimage, h0 0 (le_refl 0)]  },
  { rwa [univ_inter, mem_preimage, h1 1 (le_refl 1)]  },
  contrapose! hi,
  rw [univ_inter, ←preimage_inter] at hi,
  cases hi with z hz,
  use [f z, hr ⟨z, rfl⟩, hz],
end

/-- A set is path-connected if it is nonempty and pre-path-connected. -/
def is_path_connected (A : set α) := A.nonempty ∧ is_pre_path_connected A

theorem is_path_connected.nonempty (h : is_path_connected A) : A.nonempty := h.left
theorem is_path_connected.is_pre_path_connected (h : is_path_connected A) :
  is_pre_path_connected A := h.right

theorem is_path_connected_singleton {a} : is_path_connected ({a} : set α) :=
⟨⟨a, rfl⟩, λ ⟨x, hx⟩ ⟨y, hy⟩, by convert are_path_connected.refl ⟨a, mem_singleton a⟩⟩

lemma is_path_connected_iff : is_path_connected A ↔ (∃ x : A, ∀ y : A, are_path_connected x y) :=
⟨λ ⟨⟨w, hw⟩, ha⟩, ⟨⟨w, hw⟩, λ x, ha ⟨w, hw⟩ x⟩,
λ ⟨⟨w, hw⟩, ha⟩, ⟨⟨w, hw⟩, λ x y, trans (symm (ha x)) (ha y)⟩⟩

theorem is_path_connected.is_connected (h : is_path_connected A): is_connected A :=
⟨h.left, is_pre_path_connected.is_pre_connected h.right⟩

theorem is_path_connected.union {s t : set α} (hst : (s ∩ t).nonempty)
  (hs : is_path_connected s) (ht : is_path_connected t) : is_path_connected (s ∪ t) :=
let ⟨x, hxs, hxt⟩ := hst in
⟨⟨x, or.inl hxs⟩, is_pre_path_connected.union x hxs hxt hs.right ht.right⟩

theorem is_path_connected.image {s : set α} (H : is_path_connected s) (f : α → β)
  (hf : continuous_on f s) : is_path_connected (f '' s) :=
let ⟨x, hx⟩ := H.1 in ⟨⟨f x, mem_image_of_mem f hx⟩, is_pre_path_connected.image H.2 f hf⟩

/-- The path component of a point is the maximal path connected set containing this point. -/
def path_component (x) := ⋃₀ {s : set α | is_pre_path_connected s ∧ x ∈ s}

theorem mem_path_component {x : α} : x ∈ path_component x :=
mem_sUnion_of_mem (mem_singleton x) ⟨is_path_connected_singleton.right, mem_singleton x⟩

theorem is_path_connected_path_component {x : α} : is_path_connected (path_component x) :=
⟨⟨x, mem_path_component⟩, is_pre_path_connected_sUnion x (λ _, and.right) (λ _, and.left)⟩

theorem subset_path_component {x : α} {A : set α} (ha : is_pre_path_connected A) (hx : x ∈ A) :
  A ⊆ path_component x := λ z hz, mem_sUnion_of_mem hz ⟨ha, hx⟩

theorem path_component.subset_connected_component (x : α) :
  path_component x ⊆ connected_component x :=
subset_connected_component
  (is_pre_path_connected.is_pre_connected is_path_connected_path_component.right)
  mem_path_component

/-- A path connected space is one where all points are path connected. -/
class pre_path_connected_space (α : Type*) [topological_space α] : Prop :=
(is_pre_path_connected_univ [] : is_pre_path_connected (univ : set α))

section prio
set_option default_priority 100 -- see Note [default priority]
/-- A path connected space is a nonempty one where all points are path connected. -/
class path_connected_space (α : Type*) [topological_space α]
extends pre_path_connected_space α : Prop := (to_nonempty : nonempty α)
end prio

lemma subtype.pre_path_connected_space (hA : is_pre_path_connected A) :
  pre_path_connected_space A :=
⟨λ a b,
let ⟨p, hp0, hp1, hpr, hpc⟩ := hA a b in
⟨(λ x, ⟨p x, hpr $ mem_range_self _⟩),
λ x hx, by simp [hp0 x hx],
λ x hx, by simp [hp1 x hx],
subset_univ _,
continuous_subtype_mk _ hpc⟩⟩

theorem is_pre_path_connected_univ [h : pre_path_connected_space α] :
is_pre_path_connected (univ : set α) := h.1

lemma subtype.path_connected_space (hA : is_path_connected A) :
  path_connected_space A :=
{ is_pre_path_connected_univ := (subtype.pre_path_connected_space hA.right).1,
  to_nonempty := hA.nonempty.to_subtype }

theorem exists_path [pre_path_connected_space α] (a b) :
  ∃ f : ℝ → α, (∀ x ≤ 0, f x = a) ∧ (∀ x, 1 ≤ x → f x = b) ∧ continuous f :=
let ⟨p, hp0, hp1, _, hpc⟩ := is_pre_path_connected_univ ⟨a, mem_univ a⟩ ⟨b, mem_univ b⟩ in
⟨p, hp0, hp1, hpc⟩

theorem exists_path' [pre_path_connected_space α] (a b) :
  ∃ f : ℝ → α, f 0 = a ∧ f 1 = b ∧ continuous_on f I01 :=
let ⟨p, hp0, hp1, _, hpc⟩ :=
  are_path_connected_iff.mp (is_pre_path_connected_univ ⟨a, mem_univ a⟩ ⟨b, mem_univ b⟩) in
⟨p, hp0, hp1, hpc⟩

-- This section proves a classic counterexample which is connected but not path-connected.
section comb_space
open complex metric
/-- The horizontal closed line segment between (x₁, y) and (x₂, y) -/
def hor_Icc (y x1 x2 : ℝ) : set ℂ := {z | z.im = y ∧ z.re ∈ Icc x1 x2}
/-- The vertical closed line segment between (x, y₁) and (x, y₂) -/
def ver_Icc (x y1 y2 : ℝ) : set ℂ := {z | z.re = x ∧ z.im ∈ Icc y1 y2}

/-- The comb space without the zero bristle in ℂ -/
def partial_comb := (⋃ (n : ℕ), ver_Icc (1/n.succ) 0 1) ∪ hor_Icc 0 0 1
/-- The deleted comb space in ℂ -/
def deleted_comb := partial_comb ∪ {I}

example : is_connected deleted_comb :=
begin
  refine ⟨⟨0, or.inl $ or.inr ⟨rfl, zero_re ▸ (left_mem_Icc.mpr zero_le_one)⟩⟩,
    is_preconnected.dense_subset (subset_union_left _ _) (union_subset subset_closure $
    singleton_subset_iff.mpr $ metric.mem_closure_iff.mpr $ λ e hep, _)
    (is_pre_path_connected.is_pre_connected _)⟩,
  { cases exists_nat_one_div_lt hep with n hn,
    use [⟨1/(n+1), 1⟩, or.inl $ mem_Union.mpr ⟨n, rfl, right_mem_Icc.mpr zero_le_one⟩],
    rwa [mk_eq_add_mul_I, of_real_one, one_mul, dist_comm,
      dist_eq, add_sub_cancel, abs_of_real, abs_of_pos],
    apply one_div_pos_of_pos,
    exact_mod_cast nat.succ_pos n },
  have mul_I01 : ∀ {a b}, a ∈ I01 → b ∈ I01 → a * b ∈ I01 := λ a b ⟨ha0, ha1⟩ ⟨hb0, hb1⟩,
    ⟨zero_mul (0:ℝ) ▸ mul_le_mul ha0 hb0 (le_refl 0) ha0,
    one_mul (1:ℝ) ▸ mul_le_mul ha1 hb1 hb0 (zero_le_one)⟩,
  unfold partial_comb,
  rw Union_union,
  refine is_pre_path_connected_Union 0 (λ _, or.inr ⟨rfl, left_mem_Icc.mpr zero_le_one⟩) (λ n,
    is_pre_path_connected.union ⟨1/n.succ, 0⟩ ⟨rfl, left_mem_Icc.mpr zero_le_one⟩ ⟨rfl, _⟩ _ _);
  try {apply is_path_connected.is_pre_path_connected ∘ is_path_connected_iff.mpr},
      split,
      { norm_num, norm_cast, linarith },
    { rw div_le_iff; norm_num, norm_cast, linarith  },
  { refine ⟨⟨⟨1/n.succ, 0⟩, ⟨rfl, left_mem_Icc.mpr zero_le_one⟩⟩, _⟩,
    rintro ⟨y, hyr, hyi⟩,
    refine are_path_connected_iff.mpr ⟨λ x, ⟨y.re, y.im * x⟩ , _⟩,
    rw [mul_zero, mul_one],
    refine ⟨congr_arg coe hyr, eta y, _, continuous.continuous_on _⟩,
    { rintro _ ⟨x, hx, rfl⟩,
      exact ⟨hyr, mul_I01 hyi hx⟩ },
    rw @funext _ _ (λ x, (⟨y.re, y.im * x⟩ : ℂ)) _ (λ x, mk_eq_add_mul_I (y.re) (y.im * x)),
    refine continuous.add continuous_const (continuous.mul _ continuous_const),
    exact continuous.comp continuous_of_real (continuous.mul continuous_const continuous_id)  },
  refine ⟨⟨0, rfl, left_mem_Icc.mpr zero_le_one⟩, _⟩,
  rintro ⟨y, hyi, hyr⟩,
  refine are_path_connected_iff.mpr ⟨λ x, y * x , _⟩,
  norm_cast,
  refine ⟨mul_zero y, mul_one y, _, _⟩,
  { rintro _ ⟨x, hx, rfl⟩,
    use [by norm_num [hyi], by norm_num [mul_I01 hyr hx]] },
  exact continuous.continuous_on (continuous.mul continuous_const continuous_of_real),
end

/-- The set of reciprocals of the natural numbers in ℝ is totally disconnected. -/
theorem is_totally_disconnected_nat_reciprocals :
  is_totally_disconnected {t : ℝ | ∃ n : ℕ, t = 1/n} :=
begin
 intros s hsk hs,
  constructor,
  rintro ⟨x, hx⟩ ⟨r, hr⟩,
  rw subtype.mk_eq_mk,
  by_contra hw,
  replace hw := lt_or_gt_of_ne hw,
  wlog := hw using x r,
  obtain ⟨x, rfl⟩ := hsk hx,
  obtain ⟨_ | r, rfl⟩ := hsk hr,
  { norm_num at hw, norm_cast at hw, linarith  },
  have hhqr : (1:ℝ)/r.succ.succ < 1/r.succ,
  { refine one_div_lt_one_div_of_lt (by exact_mod_cast nat.succ_pos _) _,
    exact_mod_cast lt_add_one _ },
  by_cases hx1 : x = 1,
  { rw hx1 at hw,
    replace hw := lt_of_one_div_lt_one_div (by norm_num) hw,
    norm_num at hw, norm_cast at hw, linarith  },
  have hhql : (1:ℝ)/x ≤ 1/r.succ.succ,
  { obtain _ | _ | x := x,
      { norm_num, norm_cast, linarith  },
    { contradiction },
  { refine one_div_le_one_div_of_le (by exact_mod_cast nat.succ_pos _) _,
    replace hw := lt_of_one_div_lt_one_div (by exact_mod_cast nat.succ_pos _) hw,
    norm_num at hw ⊢, norm_cast at hw ⊢, linarith  }},
  obtain ⟨q, hql, hqr⟩ := exists_rat_btwn hhqr,
  obtain ⟨w, _, hww⟩ := hs (Iio q) (Ioi q) is_open_Iio is_open_Ioi (λ w hw, _)
    ⟨1/x, hx, lt_of_le_of_lt hhql hql⟩ ⟨1/r.succ, hr, hqr⟩,
  { change w < q ∧ w > q at hww, cases hww, linarith },
  obtain ⟨_ | w, rfl⟩ := hsk hw,
  { exact or.inl (lt_trans (by norm_num; norm_cast; linarith) hql)  },
  by_cases hwp : (1:ℝ)/w.succ ≥ 1/r.succ,
  { exact or.inr (lt_of_lt_of_le hqr hwp)  },
  suffices heq : (1:ℝ)/w.succ ≤ 1/r.succ.succ,
  { exact or.inl (lt_of_le_of_lt heq hql) },
  refine one_div_le_one_div_of_le (by exact_mod_cast nat.succ_pos _) _,
  replace hw := lt_of_one_div_lt_one_div (by exact_mod_cast nat.succ_pos _) (not_le.mp hwp),
  norm_num at hw ⊢, norm_cast at hw ⊢, linarith
end

example : ¬ is_pre_path_connected deleted_comb :=
begin
  let V := ball I (1/2),
  have hV : ∀ x ∈ V, x ∈ deleted_comb → x = I ∨ x.im ∈ I01 ∧ ∃ n : ℕ, x.re = 1/n.succ,
  { rintro z hzv (⟨⟨_, ⟨n, rfl⟩, ⟨hfr, hfi⟩⟩ | ⟨hfi, hfr0, hfr1⟩⟩ | hc),
      { exact or.inr ⟨hfi, n, hfr⟩  },
    { change abs (z - I) < 1/2 at hzv,
      replace hzv := lt_of_le_of_lt (abs_im_le_abs _) hzv,
      rw [sub_im, hfi] at hzv,
      norm_num at hzv },
    exact or.inl (mem_singleton_iff.mp hc)  },
  intros hw,
  obtain ⟨f, hf0, hf1, hfr, hfc⟩ :=
    hw ⟨I, singleton_subset_iff.mp $ subset_union_of_subset_right subset.rfl _⟩
    ⟨0, or.inl $ or.inr ⟨rfl, zero_re ▸ (left_mem_Icc.mpr zero_le_one)⟩⟩,
  let A := f ⁻¹' {I},
  suffices hA : is_open A,
  { cases is_clopen_iff.mp ⟨hA, continuous_iff_is_closed.mp hfc _ is_closed_singleton⟩ with h h,
    { exact (subset.antisymm_iff.mp h).left (hf0 0 (le_refl 0)) },
    have hw1 : (1:ℝ) ∈ A := h.symm ▸ mem_univ 1,
    rw [mem_preimage, hf1 1 (le_refl 1), mem_singleton_iff] at hw1,
    injections, linarith  },
  rw is_open_iff,
  intros x hx,
  change f x = I at hx,
  obtain ⟨d, hdp, hd⟩ := (continuous_iff.mp hfc) x (1/2) (by norm_num),
  rw hx at hd,
  use [d, hdp],
  intros z hz,
  obtain hzp | ⟨hi, n, hr⟩ := hV (f z) (hd z hz) (hfr ⟨z, rfl⟩),
  { assumption },
  suffices hs : subsingleton (re ∘ f '' ball x d),
  { cases hs with hs,
    specialize hs ⟨(f z).re, z, hz, rfl⟩ ⟨0, x, mem_ball_self hdp, by norm_num [hx]⟩,
    rw subtype.mk_eq_mk.mp hs at hr,
    replace hr := eq_zero_of_one_div_eq_zero hr.symm,
    norm_cast at hr },
  apply is_totally_disconnected_nat_reciprocals,
  { rintro s ⟨r, hr, rfl⟩,
    obtain hsp | ⟨hsi, m, hsr⟩ := hV (f r) (hd r hr) (hfr ⟨r, rfl⟩),
    { use 0, norm_num [hsp]  },
    use m.succ, norm_num [hsr]  },
  refine is_preconnected.image _ _ (continuous.continuous_on (continuous.comp continuous_re hfc)),
  exact (real.ball_eq_Ioo x d).symm ▸ is_preconnected_Ioo,
end

end comb_space

example (A : set ℝ) : is_pre_path_connected A ↔ is_preconnected A :=
begin
  refine ⟨is_pre_path_connected.is_pre_connected, λ h a b, _⟩,
  wlog := le_total a b using a b;
    try {exact symm this},
  refine are_path_connected_iff.mpr ⟨λ x, a + (b - a) * x, by norm_num, by norm_num,
    trans _ $ (is_preconnected_iff_forall_Icc_subset.mp h) a b a.2 b.2 case,
    continuous_on_const.add $ continuous_on_const.mul continuous_on_id⟩,
  rintro _ ⟨x, hx, rfl⟩,
  use [(le_add_iff_nonneg_right _).mpr $ mul_nonneg (sub_nonneg.mpr case) hx.1,
    le_sub_iff_add_le'.mp $ mul_le_of_le_one_right (sub_nonneg.mpr case) hx.2],
end

/--A set is `preconnected` iff continuous functions from it to a discrete two-space are constant.-/
theorem is_preconnected_iff_continuous_const : is_preconnected A ↔
  ∀ f : α → ({0,1} : set ℝ), continuous_on f A → subsingleton (f '' A) :=
begin
  split,
  { intros hA f hfc,
    split,
    rintro ⟨_, ⟨x, hx, rfl⟩⟩ ⟨_, ⟨y, hy, rfl⟩⟩,
    obtain hw := is_totally_disconnected_nat_reciprocals _ _
      (is_preconnected.image hA (λ x, (f x).1) (continuous_subtype_coe.comp_continuous_on hfc)),
    { exact subtype.mk_eq_mk.mpr (subtype.eq $ subtype.mk_eq_mk.mp $
        hw ⟨f x, x, hx, rfl⟩ ⟨f y, y, hy, rfl⟩) },
    rintro _ ⟨w, hw, rfl⟩,
    cases (f w).2 with h h,
    { use 0, norm_num [h] },
    use 1, norm_num [mem_singleton_iff.mp h]  },
  intro h,
  classical,
  by_contra hw,
  unfold is_preconnected at hw,
  push_neg at hw,
  rcases hw with ⟨U, V, huo, hvo, hc, ⟨x, hxa, hxu⟩, ⟨y, hya, hyv⟩, he⟩,
  obtain hw := h (λ x, if x ∈ U then ⟨0, or.inl rfl⟩ else ⟨1, or.inr $ mem_singleton 1⟩) _,
  { specialize hw ⟨⟨0, or.inl rfl⟩, x, hxa, if_pos hxu⟩
      ⟨⟨1, or.inr $ mem_singleton 1⟩, y, hya, if_neg (λ hw, he ⟨y, hya, hw, hyv⟩)⟩,
    injections, linarith  },
  rw continuous_on_iff,
  intros a haa T hto h01,
  split_ifs at h01 with hau hnau,
  { rw [if_preimage, preimage_const, if_pos h01, inter_univ],
    use [U, huo, hau, trans (inter_subset_left U A) (subset_union_left U _)]  },
  rw [if_preimage, union_comm, preimage_const, if_pos h01, inter_univ],
  use [V, hvo, or.resolve_left (hc haa) hau,
    subset_union_of_subset_left (λ w ⟨hwv, hwa⟩ hwu, he ⟨w, hwa, hwu, hwv⟩) _],
end