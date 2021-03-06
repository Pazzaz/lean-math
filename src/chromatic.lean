import topology.metric_space.basic
import data.fintype.basic
import data.real.basic
import mod_two

universe u

/-- Whether a space can be colored using n colors while avoiding monochrome
    pairs with distances in `D`. -/
def space_colorable
(X : Type u) [has_dist X]
(D : finset ℝ)
(n : ℕ)
: Prop
:= ∃ (f : X → ℕ), (∀ a, f a < n) ∧ ∀ a b, (dist a b) ∈ D → f a ≠ f b


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
  let hhh : ∀(a : X), k1 a < n+1 := begin
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
  simp,
  intro k,
  exact chrom_larger X D _ k,
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
  have hpos : a - b < 1, by linarith,
  have hpos_neg : -(a - b) < 1, by linarith,
  have abs_bound : abs (a - b) < 1, by { exact max_lt hpos hpos_neg },
  linarith,

  have hmtb : ite (mod_two b < 1) 0 1 = 1, { exact if_neg hbf },
  linarith,

  have hmta : ite (mod_two a < 1) 0 1 = 1, { exact if_neg haf },
  rw hmta at ᾰ_1,
  have hbf : ¬(mod_two b < 1), by {
    intros aaaa,
    have dsmdkskd := ᾰ_1.symm,
    simp at dsmdkskd,
    exact dsmdkskd aaaa,
  },
  rw (bounding_id b bu bl) at hbf,
  have haf_expand : ¬mod_two a < 1 := haf,
  rw (bounding_id a au al) at haf_expand, 
  have hpos : a - b < 1, by linarith,
  have hpos_neg : -(a - b) < 1, by linarith,
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
  have alpha_modded : dist (mod_two a) (mod_two b) = 1 := dist_mod_two_eq_dist a b ᾰ,
  rw ←mod_two_idempotent a at ᾰ_1,
  rw ←mod_two_idempotent b at ᾰ_1,
  exact (chrom_of_real_line_bounded_contradiction
    alpha_modded
    ᾰ_1
    (ge_iff_le.mp (mod_two_geq_0 a))
    (mod_two_le_2 a)
    (ge_iff_le.mp (mod_two_geq_0 b))
    (mod_two_le_2 b)
  ),
end