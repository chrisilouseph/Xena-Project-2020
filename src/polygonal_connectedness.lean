/-
Copyright (c) 2020 Chrisil Ouseph. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chrisil Ouseph
-/

import analysis.complex.basic tactic

/-!
# Polygonally-Connected & Step-Connected Sets in Complex Numbers and Regions

This file defines polygonal-connectedness and step-connectedness (polygonal-connectedness using
only horizontal and vertical line segments) for pairs of points as well as subsets of ℂ along with
regions (domains) in topological spaces. We prove basic related theorems, like step-connectedness
implies polygonal-connectedness and all regions in ℂ are step-connected.

## Important definitions

* `are_poly_connected` : polygonal-connectedness for pairs of complex numbers
* `is_poly_connected` : polygonal-connectedness for subsets of complex numbers
* `are_step_connected` : step-connectedness for pairs of complex numbers
* `is_step_connected` : step-connectedness for subsets of complex numbers
* `is_region` : regions (also called domains, i.e. open and connected sets) of a topological space

## Implementation notes

All the above properties are implemented as `Prop`. The pairwise properties are implemented as
inductive types, producing a `Prop`.

## References

J. Bak, D. J. Newman : *Complex Analysis* : https://www.springer.com/gp/book/9781441972873
-/

open complex set
variables z1 z2 z3: ℂ
variable A : set ℂ
variables l : list ℂ
variable rp : {r : ℝ // 0 < r}

/-- The closed line segment between two complex numbers -/
def cIcc := {z : ℂ | ∃ t ∈ set.Icc (0 : ℝ) 1, z = z1 + ↑t * (z2 - z1)}

lemma cIcc_endpoints : z1 ∈ cIcc z1 z2 ∧ z2 ∈ cIcc z1 z2 :=
⟨⟨0, left_mem_Icc.mpr zero_le_one, by norm_cast; ring⟩,
⟨1, right_mem_Icc.mpr zero_le_one, by norm_cast; ring⟩⟩

lemma cIcc_self : cIcc z1 z1 = {z1} :=
begin
  refine antisymm _ (singleton_subset_iff.mpr (cIcc_endpoints z1 z1).left),
  rintros z ⟨t, ht, rfl⟩,
  rw mem_singleton_iff,
  ring
end

lemma cIcc_symm : cIcc z1 z2 = cIcc z2 z1 :=
begin
  apply subset.antisymm;
  { rintros z ⟨t, ⟨ht0, ht1⟩, rfl⟩,
    refine ⟨1-t, ⟨_, _⟩, _⟩;
      try { linarith  },
    push_cast,
    ring  }
end

/-- Two complex numbers are polygonally-connected in a set `A` iff
the line segment joining them is in `A` or by transitivity. -/
inductive are_poly_connected (A : set ℂ) : ℂ → ℂ → Prop
| line {z1 z2 : ℂ} : cIcc z1 z2 ⊆ A → are_poly_connected z1 z2
| poly_trans {z1 z2 z3 : ℂ} :
  are_poly_connected z1 z3 → are_poly_connected z3 z2 → are_poly_connected z1 z2

open are_poly_connected

lemma are_poly_connected_refl {A z1} (h : z1 ∈ A) : are_poly_connected A z1 z1 :=
by apply line; rwa [cIcc_self, singleton_subset_iff]

lemma are_poly_connected_symm {A z1 z2} (h12 : are_poly_connected A z1 z2) :
  are_poly_connected A z2 z1 :=
begin
  induction h12,
  case line : z3 z4 hl
  { apply line,
    rwa cIcc_symm },
  case poly_trans : _ _ _ _ _ h53 h45
  { exact poly_trans h45 h53  }
end

lemma are_poly_connected_trans {z1 z2 z3 A}
  (h12 : are_poly_connected A z1 z2) (h23 : are_poly_connected A z2 z3) :
  are_poly_connected A z1 z3 := poly_trans h12 h23

lemma are_poly_connected_mono {z1 z2 A B} (hs : A ⊆ B) (h : are_poly_connected A z1 z2) :
  are_poly_connected B z1 z2 :=
begin
  induction h,
  case line : z3 z4 hl
  { exact line (set.subset.trans hl hs) },
  case poly_trans : z3 z4 z5 h35 h54 h53 h45
  { exact poly_trans h53 h45  }
end
/-- A set is polygonally-connected if each pair of points in it is. -/
def is_poly_connected := ∀ {z1 z2}, z1 ∈ A → z2 ∈ A → are_poly_connected A z1 z2

/-- Two complex numbers are step-connected in a set `A` if they are connected by a
horizontal or vertical line in `A` or by transitivity. -/
inductive are_step_connected (A : set ℂ) : ℂ → ℂ → Prop
| hor {z1 z2 : ℂ} : z1.im = z2.im → cIcc z1 z2 ⊆ A → are_step_connected z1 z2
| ver {z1 z2 : ℂ} : z1.re = z2.re → cIcc z1 z2 ⊆ A → are_step_connected z1 z2
| step_trans {z1 z2 z3 : ℂ} :
  are_step_connected z1 z3 → are_step_connected z3 z2 → are_step_connected z1 z2

open are_step_connected

lemma are_step_connected_refl {A z1} (h : z1 ∈ A) : are_step_connected A z1 z1 :=
by apply hor rfl; rwa [cIcc_self, singleton_subset_iff]

lemma are_step_connected_trans {z1 z2 z3 A} (h12 : are_step_connected A z1 z2)
(h23 : are_step_connected A z2 z3) : are_step_connected A z1 z3 := step_trans h12 h23

lemma are_step_connected_symm {A z1 z2} (h12 : are_step_connected A z1 z2) :
  are_step_connected A z2 z1 :=
begin
  induction h12,
  case hor : z3 z4 hi hl
  { apply hor hi.symm,
    rwa cIcc_symm },
  case ver : z3 z4 hr hl
  { apply ver hr.symm,
    rwa cIcc_symm },
  case step_trans : z3 z4 z5 h35 h54 h53 h45
  { exact step_trans h45 h53  }
end

lemma are_step_connected_mem {z1 z2 A} (h : are_step_connected A z1 z2) : z1 ∈ A ∧ z2 ∈ A:=
begin
  induction h,
  case hor : z3 z4 hi hl
  { use [hl (cIcc_endpoints _ _).left, hl (cIcc_endpoints _ _).right] },
  case ver : z3 z4 hr hl
  { use [hl (cIcc_endpoints _ _).left, hl (cIcc_endpoints _ _).right] },
  case step_trans : z3 z4 z5 h35 h54 h53 h45
  { use [h53.left, h45.right] }
end

lemma are_poly_connected_of_are_step_connected {A z1 z2}
  (h12 : are_step_connected A z1 z2) : are_poly_connected A z1 z2 :=
begin
  induction h12,
  case hor : z3 z4 hi hl
  { exact line hl },
  case ver : z3 z4 hr hl
  { exact line hl },
  case step_trans : _ _ _ _ _ h1 h2
  { exact are_poly_connected_trans h1 h2  }
end

lemma are_step_connected_mono {z1 z2 A B} (hs : A ⊆ B) (h : are_step_connected A z1 z2):
  are_step_connected B z1 z2 :=
begin
  induction h,
  case hor : z3 z4 hi hl
  { exact hor hi (set.subset.trans hl hs) },
  case ver : z3 z4 hr hl
  { exact ver hr (set.subset.trans hl hs) },
  case step_trans : _ _ _ _ _ h1 h2
  { exact step_trans h1 h2  }
end

/-- A set is step-connected if each pair of points in it is. -/
def is_step_connected := ∀ {z1 z2}, z1 ∈ A → z2 ∈ A → are_step_connected A z1 z2

lemma is_poly_connected_of_is_step_connected {A} (h : is_step_connected A) :
  is_poly_connected A := λ x y hx hy, are_poly_connected_of_are_step_connected (h hx hy)

open metric

lemma is_step_connected_ball : is_step_connected (ball z1 ↑rp) :=
begin
  suffices heq : ∀ z ∈ ball z1 ↑rp, are_step_connected (ball z1 ↑rp) z z1,
  { intros x y hx hy,
    exact are_step_connected_trans (heq x hx) (are_step_connected_symm (heq y hy))},  
  intros z hz,
  apply @step_trans _ _ _ ⟨z.re, z1.im⟩,
  { refine ver rfl _,
    rintro w ⟨t, ⟨ht0, ht1⟩, rfl⟩,
    rw [mem_ball, dist_eq] at hz ⊢,
    change abs (z + _ * ⟨z.re - z.re, (z1 - z).im⟩ - z1) < _,
    rw [sub_self, ←sub_add_eq_add_sub, ←re_add_im ⟨0, _⟩],
    show abs (z - _ + _ * (0 + ↑(z1 - z).im * I)) < _,
    rw [zero_add, mul_mul_div (_ * I) (two_ne_zero'), mul_right_comm _ I],
    norm_cast,
    rw [mul_comm (im _), ←sub_conj, ←mul_one (z-z1), mul_left_comm,
      ←div_eq_mul_one_div, sub_mul (z1-z), ←add_sub_assoc, ←neg_sub z,
      ←neg_mul_eq_neg_mul, ←sub_eq_add_neg, ←mul_sub, neg_sub z, sub_eq_add_neg],
    apply lt_of_le_of_lt (complex.abs_add _ _),
    norm_cast,
    rw [complex.abs_neg, complex.abs_mul, complex.abs_mul,
      abs_conj, complex.abs_sub z1, ←mul_add, ←mul_one ↑rp],
    refine mul_lt_mul hz _ _ (le_of_lt rp.2);
    { rw [complex.abs_of_nonneg, complex.abs_of_nonneg];
      { linarith  }}},
  refine hor rfl _,
  rintro w ⟨t, ⟨ht0, ht1⟩, rfl⟩,
  rw [mem_ball, dist_eq] at *,
  rw [←sub_add_eq_add_sub],
  change abs ((⟨(z - z1).re, z1.im - z1.im⟩ : ℂ) + _ * ⟨(z1 - z).re, z1.im - z1.im⟩) < _,
  rw [sub_self],
  change complex.abs (↑(z - z1).re + _ * ↑(z1 - z).re) < _,
  norm_cast,
  rw [←one_mul (z - z1).re, ←neg_sub z, neg_re, ←neg_mul_eq_mul_neg, neg_mul_eq_neg_mul],
  rw [←add_mul, ←one_mul ↑rp, of_real_mul, complex.abs_mul, abs_of_real (re _)],
  apply mul_lt_mul' _ (lt_of_le_of_lt (abs_re_le_abs _) hz) (abs_nonneg _) (zero_lt_one),
  rw [complex.abs_of_nonneg];
  { linarith  }
end

/-- An open and preconnected set is called a region. -/
def is_region := is_open A ∧ is_preconnected A

theorem region_step_connected {A} : is_region A → is_step_connected A :=
begin
  classical,
  rintro ⟨hao, hap⟩ z1 z2 h1 h2,
  let C := {z | are_step_connected A z1 z},
  let D := A ∩ {z | ¬ are_step_connected A z1 z},
  by_contra hw,
  obtain ⟨_, _, _, _, _⟩ := hap C D _ _ _ ⟨_, ⟨h1, are_step_connected_refl h1⟩⟩ ⟨_, h2, ⟨h2, hw⟩⟩,
      { contradiction },
    { rw is_open_iff,
      rintro x hxz1,
      rcases (is_open_iff.mp hao) x (are_step_connected_mem hxz1).right with ⟨d, hdp, hb⟩,
      use [d, hdp],
      intros y hy,
      exact are_step_connected_trans hxz1 (are_step_connected_mono hb $
        is_step_connected_ball x ⟨d, hdp⟩ (mem_ball_self hdp) hy) },
  { rw is_open_iff,
    rintro x ⟨hx, hxz1⟩,
    rcases (is_open_iff.mp hao) x hx with ⟨d, hdp, hb⟩,
    use [d, hdp],
    intros y hy,
    use [hb hy],
    intro hw,
    replace hw := step_trans hw (are_step_connected_symm (are_step_connected_mono hb $
      is_step_connected_ball x ⟨d, hdp⟩ (mem_ball_self hdp) hy)),
    contradiction },
  intros z hz,
  by_cases hc : are_step_connected A z1 z,
  { exact or.inl hc  },
  exact or.inr ⟨hz, hc⟩,
end

lemma is_poly_connected_ball : is_poly_connected (ball z1 ↑rp) :=
  @is_poly_connected_of_is_step_connected (ball z1 ↑rp) (@is_step_connected_ball z1 rp)

lemma is_poly_connected_region (hA : is_region A) : is_poly_connected A :=
  @is_poly_connected_of_is_step_connected A (@region_step_connected A hA)