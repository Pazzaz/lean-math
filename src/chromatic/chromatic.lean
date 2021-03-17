-- TODO: Rewrite things using paritions / setoids?
--       The relation would then be "are the same color".
--       see `data.setoid.partition`.
import topology.metric_space.basic
import data.fintype.basic
import data.real.basic
import mod_two
import analysis.normed_space.inner_product
import data.setoid.partition
import data.int.sqrt

universe u

/-- Whether a space can be colored using n colors while avoiding monochrome
    pairs with distances in `D`. -/
def space_colorable
(X : Type u) [has_dist X]
(D : finset ℝ)
(n : ℕ)
: Prop
:= ∃ (f : X → ℕ), (∀ a, f a < n) ∧ ∀ a b, (dist a b) ∈ D → f a ≠ f b

-- In our application `r_in` is a more "fine-grained" equivalence relation than `r_out` but that
-- isn't needed for this theorem.
-- It is a little annoying to have to write out `r_in.rel` instead of `≈` but that is necessary when working with two setoids.
theorem separation
{X : Type u} [has_dist X]
(d : ℝ)
(r_in : setoid X) 
(r_out : setoid X)
(h1 : ∀ (a b : X), r_in.rel a b → dist a b < d)
(h2 : ∀ (a b : X), (¬r_in.rel a b) → r_out.rel a b → dist a b > d)
(x y : X)
(h3 : r_out.rel x y)
: dist x y ≠ d
:= begin
  by_contradiction hhh,
  rw not_not at hhh,
  have eq_imp_not_less : dist x y = d → ¬(dist x y) < d := by { intros bb, linarith, },
  have := (h2 x y ((mt (h1 x y)) (eq_imp_not_less hhh))) h3,
  linarith,
end

def hex_open_f (r : ℝ) (x y : ℝ) : Prop := (real.sqrt 3)⁻¹ + y - r < 0
                                        ∧  (real.sqrt 3)⁻¹ - y - r < 0
                                        ∧ -(real.sqrt 3)⁻¹ + y - r < 0
                                        ∧ -(real.sqrt 3)⁻¹ - y - r < 0
                                        ∧  x - (real.sqrt 3)*2⁻¹*r < 0
                                        ∧ -x - (real.sqrt 3)*2⁻¹*r < 0

def hex_left_up_ioo     (r : ℝ) (x y : ℝ) : Prop := -(real.sqrt 3)*2⁻¹*r < x ∧ x < 0      ∧ y =  x * (real.sqrt 3)⁻¹ + r
def hex_left_side_icc   (r : ℝ) (x y : ℝ) : Prop := -(r / 2) <= y      ∧ y <= r / 2 ∧ x = -(r * (real.sqrt 3)⁻¹)
def hex_left_down_ioc   (r : ℝ) (x y : ℝ) : Prop := -(real.sqrt 3)*2⁻¹*r < x ∧ x <= 0     ∧ y = -(x * (real.sqrt 3)⁻¹ + r)

-- A `hex_tile` is the open hexagon together with the three sides on the left
def hex_tile (r : ℝ) : set (ℝ×ℝ) := set_of (λ p, hex_open_f        r p.1 p.2
                                               ∨ hex_left_up_ioo   r p.1 p.2
                                               ∨ hex_left_side_icc r p.1 p.2
                                               ∨ hex_left_down_ioc r p.1 p.2)

def shift (k : (ℝ×ℝ)) (s : set (ℝ×ℝ)) : set (ℝ×ℝ) := set_of (λ p, s (p - k))


-- theorem hex_inter_hex_shift_right_eq_empty
-- : set.inter (hex_tile 1) (shift (⟨real.sqrt 3, 0⟩) (hex_tile 1)) = ∅
-- := begin
--   by_contradiction,
--   let hhh : ∃(x : ℝ×ℝ), (x : hex_tile 1) ∧ (x : (shift (⟨real.sqrt 3, 0⟩) (hex_tile 1))) := begin

--   end,
-- end

theorem inv_eq_2
(a b : ℝ)
(h : b ≠ 0)
: (1 / a) = b / (b*a)
:= begin
  exact (div_mul_right a h).symm,
end

theorem inv_eq_3
(a b c: ℝ)
(h : c ≠ 0)
: a / b = (a*c) / (b*c)
:= begin
  exact (mul_div_mul_right a b h).symm,
end


theorem inv_eq_4
(a : ℝ)
(h : a > 0)
: real.sqrt a ≠ 0
:= begin
  exact real.sqrt_ne_zero'.mpr h,
end


theorem inv_eq_5
(a : ℝ)
(h : 0 ≤ a)
: (real.sqrt a) * (real.sqrt a) = a
:= begin
  exact real.mul_self_sqrt h,
end

theorem zero_le_three
: 0 ≤ (3 : ℝ)
:= begin
  linarith,
end

theorem sub_div_add_div_eq_thing
(a b c : ℝ)
: -(a/b) + (c/b) = (-a + c) / b 
:= begin
  ring,
end

theorem div_lt_zero_imp_numerator_lt_zero
(a : ℝ)
{b : ℝ}
(h : b > 0)
: (a / b) < 0 -> a < 0
:= begin
  intro k,
  have ggg : b * (a/b) < b * 0 := (mul_lt_mul_left h).mpr k,
  rw [mul_zero b, (mul_div_cancel' a (ne_of_gt h))] at ggg,
  exact ggg,
end


theorem gfgfgdfgdsf
(a b: ℝ)
(h1 : a > 0)
(h2 : b > 0)
: a * real.sqrt b > 0
:= begin
  exact mul_pos h1 (real.sqrt_pos.mpr h2),
end

theorem sqrt_three_gt_zero
: real.sqrt 3 > 0
:= begin
  norm_num,
end

#check real.sqrt_one

theorem one_le_sqrt_three
: 1 ≤ real.sqrt 3
:= begin
  nth_rewrite 0 ←real.sqrt_one,
  refine real.sqrt_le_sqrt _,
  linarith,
end

theorem one_lt_sqrt_three
: 1 < real.sqrt 3
:= begin
  nth_rewrite 0 ←real.sqrt_one,
  refine (real.sqrt_lt zero_le_one).mpr _,
  linarith,
end


theorem sqrt_three_equat_pos
: real.sqrt 3 + (1 / real.sqrt 3) - real.sqrt 3 * (1 / 2) ≥ 0 
:= begin
  calc real.sqrt 3 + (1 / real.sqrt 3) - real.sqrt 3 * (1 / 2)
      = real.sqrt 3 + (1 / real.sqrt 3) - (real.sqrt 3 / 2) : by rw mul_one_div (real.sqrt 3) 2
  ... = (real.sqrt 3) / 2 + (1 / real.sqrt 3) : by linarith
  ... ≥ 0 : by {
    refine add_nonneg _ _,
    exact div_nonneg (le_of_lt sqrt_three_gt_zero) zero_le_two,
    exact div_nonneg zero_le_one (le_of_lt sqrt_three_gt_zero),
  }
end

theorem sqrt_three_equat_neg
: -(1 / real.sqrt 3) + real.sqrt 3 * (1 / 2) - real.sqrt 3 < 0
:= begin
  calc -(1 / real.sqrt 3) + real.sqrt 3 * (1 / 2) - real.sqrt 3
      = -(1 / real.sqrt 3) + -(real.sqrt 3) / 2 : begin
        linarith,
      end
  ... < 0 : by {
    refine add_neg _ _,
    exact neg_neg_of_pos (div_pos zero_lt_one (gt.lt sqrt_three_gt_zero)),
    rw neg_div 2 (real.sqrt 3),
    exact neg_neg_of_pos (div_pos (gt.lt sqrt_three_gt_zero) zero_lt_two),
  }
end


theorem hfhfhf
(a b: ℝ)
: (-a) / b = - (a/b)
:= begin
  exact neg_div b a
end

theorem inv_leq_one
{a : ℝ}
(h2 : 1 ≤ a)
: (1 / a) ≤ 1
:= begin
  refine (div_le_one _).mpr h2,
  linarith,
end


theorem ge_one_imp_sub_inv_ge_zero
(x: ℝ)
(h : 1 ≤ x)
: x - (1/x) ≥ 0
:= begin
  have jdjdj : ∀ (x1 : ℝ), 1 ≤ x1 -> 1/x1 ≤ x1 := by {
    intros xxx leee,
    calc (1 / xxx)
        ≤ 1 : inv_leq_one leee
    ... ≤ xxx : leee
  },
  exact sub_nonneg.mpr (jdjdj x h),
end

/- Not actually used -/
theorem sub_lt_zero_iff
{X : Type*} [ordered_add_comm_group X]
{a b : X}
: a - b < 0 ↔ b - a > 0
:= begin
  refine (iff.intro _ _),
  intro h,
  have hue := neg_lt_neg h,
  rw [neg_zero, neg_sub a b] at hue,
  exact hue,

  intro h,
  have hue := neg_lt_neg h,
  rw [neg_zero, neg_sub b a] at hue,
  exact hue,
end

theorem ge_one_imp_sub_inv_gt_zero
(x: ℝ)
(h : 1 < x)
: x - (1/x) > 0
:= begin
  have jdjdj : ∀ (x1 : ℝ), 1 < x1 -> 1/x1 < x1 := by {
    intros xxx leee,
    calc (1 / xxx)
        = xxx⁻¹ : one_div xxx
    ... < 1 : inv_lt_one leee
    ... < xxx : leee
  },
  exact sub_pos.mpr (jdjdj x h),
end



theorem another_case
{x : ℝ}
(hh7: x = -(1 / real.sqrt 3))
(hh13: x - real.sqrt 3 = -(1 / real.sqrt 3))
: false
:= begin
  rw hh7 at hh13,
  have sqrt_three_eq_zero : real.sqrt 3 = 0 := by linarith,
  rw ←real.sqrt_zero at sqrt_three_eq_zero,
  have yepp : (3 : ℝ) = 0 := by {
    refine (real.sqrt_inj _ _).mp (sqrt_three_eq_zero),
    exact zero_le_three,
    exact rfl.ge,
  },
  linarith,
end

-- How can I avoid the annoying case analysis? I should probably use rcases.
theorem in_the_middle
(x : ℝ×ℝ)
(h : (x ∈ hex_tile 1))
(h2 : (x ∈ shift (⟨real.sqrt 3, 0⟩) (hex_tile 1)))
: false
:= begin
  rw [hex_tile] at h,
  simp at *,
  rw [shift] at h2,
  rw [hex_tile] at h2,
  simp at h2,
  rw set.set_of_app_iff at h2,
  unfold hex_open_f hex_left_up_ioo hex_left_side_icc hex_left_down_ioc at h,
  unfold hex_open_f hex_left_up_ioo hex_left_side_icc hex_left_down_ioc at h2,
  simp at h,
  simp at h2,
  set xx : ℝ := x.fst,
  set yy : ℝ := x.snd,
  cases h,
  cases h2,
  have huehue21 : xx < real.sqrt 3 / 2 := by tauto,
  have huehue22 : real.sqrt 3 - xx < real.sqrt 3 / 2 := by tauto,
  linarith only [huehue21, huehue22],


  cases h2,
  have hh5 := h.2.2.2.2.1,
  have hh7 := h2.1,
  have huehue21 : xx          < real.sqrt 3 / 2      := by tauto,
  have huehue22 : real.sqrt 3 < xx + real.sqrt 3 / 2 := by tauto,
  linarith only [huehue21, huehue22],
  rw [inv_eq_one_div (real.sqrt 3), inv_eq_one_div (2 : ℝ)] at h,
  rw [inv_eq_one_div (real.sqrt 3), inv_eq_one_div (2 : ℝ)] at h2,
  cases h2,
  have hh9 := h.2.2.2.2.1,
  have hh13 := h2.2.2,
  have xxx3 : -(1 / real.sqrt 3) + (real.sqrt 3) / 2 < 0 := by linarith,
  rw (div_mul_right (real.sqrt 3) two_ne_zero).symm at xxx3,
  rw ((mul_div_mul_right (real.sqrt 3) 2 (real.sqrt_ne_zero'.mpr zero_lt_three)).symm  ) at xxx3,
  rw (real.mul_self_sqrt (zero_le_three)) at xxx3,
  rw (sub_div_add_div_eq_thing 2 (2 * real.sqrt 3) 3) at xxx3,
  let kkkkk := div_lt_zero_imp_numerator_lt_zero (-2 + 3) (mul_pos (zero_lt_two) sqrt_three_gt_zero) xxx3,
  linarith only [kkkkk],
  linarith,
  rw [inv_eq_one_div (real.sqrt 3), inv_eq_one_div (2 : ℝ)] at h,
  rw [inv_eq_one_div (real.sqrt 3), inv_eq_one_div (2 : ℝ)] at h2,
  cases h2,
  cases h,
  linarith,
  cases h,
  have hh10 := h2.2.2.2.2.2,
  have hh13 := h.2.2,
  rw hh13 at hh10,
  norm_num at hh10,
  have huehue : real.sqrt 3 + (1 / real.sqrt 3) - real.sqrt 3 * (1 / 2) < 0 := sub_lt_zero.mpr hh10,
  let llll := sqrt_three_equat_pos,
  linarith,
  linarith,
  cases h2,
  cases h,
  linarith,
  cases h,
  have hh7 := h.2.2,
  have hh11 := h2.1,
  rw hh7 at hh11,
  have huehue : 0 < -(1 / real.sqrt 3) + real.sqrt 3 * (1 / 2) - real.sqrt 3 := sub_pos.mpr hh11,
  let llll := sqrt_three_equat_neg,
  linarith,
  linarith,
  cases h2,
  cases h,

  have hh6 := h.2.1,
  have hh13 := h2.2.2,
  have djdjdjdj : xx = -(1 / real.sqrt 3) + real.sqrt 3 := begin
    linarith,
  end,
  rw djdjdjdj at hh6,
  have hh99 : (real.sqrt 3) - (1/ (real.sqrt 3)) ≥ 0 := begin
    exact ge_one_imp_sub_inv_ge_zero (real.sqrt 3) one_le_sqrt_three,
  end,
  linarith,
  cases h,
  exact another_case h.2.2 h2.2.2,

  have hh6 := h.2.1,
  have hh13 := h2.2.2,
  have djdjdjdj : xx = -(1 / real.sqrt 3) + real.sqrt 3 := begin
    linarith,
  end,
  rw djdjdjdj at hh6,
  have hh99 : (real.sqrt 3) - (1/ (real.sqrt 3)) > 0 := begin
    exact ge_one_imp_sub_inv_gt_zero (real.sqrt 3) one_lt_sqrt_three,
  end,
  linarith,
  cases h,
  linarith,
  cases h,
  sorry,
  sorry,
end




theorem simple_hfhfhf
: ((1*1) - 1)/1 = 0
:= by simp


-- theorem step_simple_hfhfhf
-- (h1: xx = -(1 / real.sqrt 3))
-- hh11: -(1 / 2) ≤ yy
-- hh12: yy ≤ 1 / 2
-- hh13: xx - real.sqrt 3 = -(1 / real.sqrt 3)
-- := begin
--   ring,
--   finish,
-- end



/-

  have hh5 := h.1,
  have hh6 := h.2.1,
  have hh7 := h.2.2.1,
  have hh8 := h.2.2.2.1,
  have hh9 := h.2.2.2.2.1,
  have hh10 := h.2.2.2.2.2,
  have hh11 := h2.1,
  have hh12 := h2.2.1,
  have hh13 := h2.2.2,
-/

/- 
-(Sqrt[3] * (1 / 2)) < x
&& x ≤ 0
&& y = -1 + -(x * (1 / Sqrt[3]))
&& -(1 / 2) ≤ y
&& y ≤ 1 / 2
&& x - Sqrt[3] = -(1 / Sqrt[3])
-/


theorem hex_inter_hex_shift_right_eq_empty_imp_shift_le_sqrt_three
(x : ℝ)
: set.inter (hex_tile 1) (shift (⟨x, 0⟩) (hex_tile 1)) = ∅ → real.sqrt 3 ≤ x
:= sorry

theorem hex_inter_hex_shift_right_eq_empty_imp_shift_le_scale_mul_sqrt_three
(x : ℝ)
(s : ℝ)
: set.inter (hex_tile s) (shift (⟨x, 0⟩) (hex_tile s)) = ∅ → s * real.sqrt 3 ≤ x
:= sorry

/-- An inhabitated space cannot be colored with 0 colors -/
theorem chrom_absurd
(X : Type u) [has_dist X] [inhabited X]
(D : finset ℝ)
(n : ℕ)
: ¬space_colorable X D 0
:= begin
  rw space_colorable,
  simp,
end

theorem chrom_larger
(X : Type u) [has_dist X]
(D : finset ℝ)
(n : ℕ)
: space_colorable X D n → space_colorable X D (n+1)
:= begin
  rw [space_colorable, space_colorable],
  intro f1,
  refine exists.elim f1 _,
  intros k1 k2,
  have : ∀(a : X), k1 a < n+1 := begin
    intro a,
    exact nat.lt.step (k2.left a),
  end,
  tidy,
end

theorem chrom_smaller
(X : Type u) [has_dist X]
(D : finset ℝ)
(n : ℕ)
: ¬space_colorable X D n → ¬space_colorable X D (n-1)
:= begin
  refine not_imp_not.mpr _,
  induction n,
  exact id,
  intro k,
  exact chrom_larger X D _ k,
end

theorem if_eq_else_imp_false
{c : Prop} [decidable c] {α : Type*} {t e : α}
(h_eq : ite c t e = e) (h_ne : t ≠ e)
: ¬c
:= begin
  by_contradiction p_pos,
  exact h_ne ((rfl.congr (if_pos p_pos)).mp (h_eq.symm)).symm,
end

theorem if_eq_then_imp_true
{c : Prop} [decidable c] {α : Type*} {t e : α}
(h_eq : ite c t e = t) (h_ne : t ≠ e)
: c
:= begin
  by_contradiction p_neg,
  exact h_ne ((rfl.congr (if_neg p_neg)).mp (h_eq.symm)),
end

theorem chrom_of_real_line_bounded_contradiction
{a b: ℝ}
(ᾰ: dist a b = 1)
(ᾰ_1: ite (mod_two a < 1) 0 1 = ite (mod_two b < 1) 0 1)
(al : 0 ≤ a)
(au : a < 2)
(bl : 0 ≤ b)
(bu : b < 2)
: false
:= begin
  cases decidable.em (mod_two a < 1) with hat haf,
  rw (if_pos hat) at ᾰ_1,
  cases decidable.em (mod_two b < 1) with hbt hbf,
  rw (if_pos hbt) at ᾰ_1,
  rw real.dist_eq at ᾰ,
  have hhha : a < 1 := bounding_mod_two a au al hat,
  have hhhb : b < 1 := bounding_mod_two b bu bl hbt,
  have hpos : a - b < 1,            by linarith,
  have hpos_neg : -(a - b) < 1,     by linarith,
  have abs_bound : abs (a - b) < 1, by { exact max_lt hpos hpos_neg },
  linarith,

  have hmtb : ite (mod_two b < 1) 0 1 = 1, { exact if_neg hbf },
  linarith,

  have hmta : ite (mod_two a < 1) 0 1 = 1, { exact if_neg haf },
  rw hmta at ᾰ_1,
  have hbf : ¬(mod_two b < 1) := if_eq_else_imp_false ᾰ_1.symm zero_ne_one,
  rw (bounding_id b bu bl) at hbf,
  have haf_expand : ¬mod_two a < 1 := haf,
  rw (bounding_id a au al) at haf_expand,
  have hpos : a - b < 1,            by linarith,
  have hpos_neg : -(a - b) < 1,     by linarith,
  have abs_bound : abs (a - b) < 1, by { exact max_lt hpos hpos_neg },
  rw real.dist_eq at ᾰ,
  exact ne_of_lt abs_bound ᾰ,
end

theorem dist_mod_two_eq_dist
(x y : ℝ)
(h : dist x y = 1)
: dist (mod_two x) (mod_two y) = 1
:= begin
  rw real.dist_eq at h,
  rw real.dist_eq,

  cases decidable.em (x > y) with x_ge_y ne_x_ge_y, by
  {
    rw (abs_of_pos (sub_pos.mpr x_ge_y)) at h,
    have y_simp : y = x-1, by linarith,
    rw y_simp,
    exact (abs_of_mod_two_sub_mod_two_of_sub_one_eq_one x),
  },
  {
    have abs_simp : abs (x - y) = y - x, by { have := abs_sub x y, finish, },
    rw abs_simp at h,
    have y_simp : x = y-1, by linarith,
    rw y_simp,
    rw abs_sub (mod_two (y - 1)) (mod_two y),
    exact (abs_of_mod_two_sub_mod_two_of_sub_one_eq_one y),
  }
end

/-- A coloring of the real line used in `real_line_colorable_avoiding_one_with_two`. -/
private noncomputable def line_color (x : ℝ) : ℕ := ite (mod_two x < 1) 0 1

/-- The real number line can be colored with two colors
    while avoiding monochrome unit distances. --/
theorem colorable_real_line_avoiding_one_with_two
: space_colorable ℝ {1} 2
:= begin
  tidy,
  exact (line_color ᾰ),
  rw line_color,
  cases decidable.em (mod_two a < 1) with H1 H2,
  rw (if_pos H1),
  exact zero_lt_two,
  rw (if_neg H2),
  exact one_lt_two,
  rw [line_color, line_color] at ᾰ_1,
  rw ←mod_two_idempotent a at ᾰ_1,
  rw ←mod_two_idempotent b at ᾰ_1,
  exact (chrom_of_real_line_bounded_contradiction
    (dist_mod_two_eq_dist a b ᾰ)
    ᾰ_1
    (ge_iff_le.mp (mod_two_geq_0 a))
    (mod_two_le_2 a)
    (ge_iff_le.mp (mod_two_geq_0 b))
    (mod_two_le_2 b)
  ),
end