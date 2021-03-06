import data.fintype.basic
import data.real.basic


@[simp]
theorem floor_add_one_real
(x : ℝ)
(az : ℤ)
{ar : ℝ}
{h : coe az = ar}
: floor (x + (ar : ℝ)) = (floor x) + az
:= begin
  rw h.symm,
  exact floor_add_int x az,
end

theorem floor_eq_iff'
{T : Type*} [linear_ordered_ring T] [floor_ring T]
(r : T)
(ru : r < 1)
(rl : 0 ≤ r)
: floor r = 0
:= begin
  have h1 : ((0 : ℤ) : T) ≤ r ∧ r < (0 + 1), by {refine ⟨rl, _⟩, finish},
  exact (floor_eq_iff.mpr h1),
end


noncomputable def mod_two (x : ℝ) : ℝ := x - 2 * (floor (x / 2))

@[simp]
theorem mod_plus_two_eq_id
(x : ℝ)
: mod_two (x+2) = mod_two x
:= begin
  unfold mod_two,
  norm_cast,
  calc  x + 2 -  ↑(2 * ⌊(x + 2) / 2⌋)
      = x + 2 -  ↑(2 * ⌊x / 2 + (2 / 2)⌋) : by rw add_div x 2 2
  ... = x + 2 -  ↑(2 * ⌊x / 2 + 1⌋)       : by {rw div_self, exact two_ne_zero }
  ... = x + 2 -  ↑(2 * (⌊x / 2⌋ + 1))     : by rw @floor_add_one_real (x/2) 1 _ (zero_add 1)
  ... = x + 2 -  ↑(2 * ⌊x / 2⌋ + 2*1)     : by rw mul_add 2 ⌊(x / 2)⌋ 1
  ... = x + 2 -  ↑(2 * ⌊x / 2⌋ + 2)       : rfl
  ... = x + 2 - (↑(2 * ⌊x / 2⌋) + 2)      : by norm_num
  ... = x     -  ↑(2 * ⌊x / 2⌋)           : by linarith
end

@[simp]
theorem mod_shift_even_eq_mod
(x : ℝ)
(k : ℤ)
: mod_two (x+2*k) = mod_two x
:= begin
  unfold mod_two,
  norm_cast,
  calc  x + ↑(2*k) -  ↑(2 * ⌊(x + ↑(2*k)) / 2⌋)
      = x + ↑(2*k) -  ↑(2 * ⌊x / 2 + (↑(2*k) / 2)⌋) : by rw add_div x ↑(2*k) 2
  ... = x + ↑(2*k) -  ↑(2 * ⌊x / 2 + ((2*↑k) / 2)⌋) : by norm_num
  ... = x + ↑(2*k) -  ↑(2 * ⌊x / 2 + ((↑k*2) / 2)⌋) : by rw mul_comm 2 (↑k : ℝ)
  ... = x + ↑(2*k) -  ↑(2 * ⌊x / 2 + (↑k : ℝ)⌋)     : by {
                                                        rw div_eq_mul_inv ((↑k*2) : ℝ) 2,
                                                        rw mul_assoc (↑k : ℝ) 2  2⁻¹,
                                                        have inverse_cancel : 2 * (2 : ℝ)⁻¹ = 1 := half_add_self 1,
                                                        rw inverse_cancel,
                                                        rw mul_one (↑k : ℝ),
                                                      }
  ... = x + ↑(2*k) -  ↑(2 * (⌊x / 2⌋ + k))          : by rw @floor_add_one_real (x/2) k _ rfl
  ... = x + ↑(2*k) -  ↑((2 * ⌊x / 2⌋) + (2*k : ℤ))  : by rw mul_add 2 ⌊(x / 2)⌋ k
  ... = x - ↑(2 * ⌊x / 2⌋)                          : by { rw int.cast_add (2 * ⌊x / 2⌋) (2 * k), ring, }
end

@[simp]
theorem bounding_id
(a : ℝ)
(au : a < 2)
(al : 0 ≤ a)
: mod_two a = a
:= begin
  calc  a - 2 * ↑⌊a / 2⌋
        = a - 2 * ↑(0)     : by {
          have hu : (a / 2) < 1, by {refine (div_lt_one _).mpr au, exact zero_lt_two},
          have hl : 0 ≤ (a / 2), by {refine div_nonneg al _,       exact zero_le_two},
          rw floor_eq_iff' (a/2) hu hl,
          exact rfl,
        }
    ... = a - 2 * 0        : rfl
    ... = a                : by linarith,
end

theorem mod_two_le_2
(x : ℝ)
: mod_two x < 2
:= begin
  calc x - 2 * ↑⌊x / 2⌋
      < x - 2 * ((x / 2) - 1 ) : by { norm_num, exact sub_one_lt_floor (x / 2), }
  ... = 2                      : by linarith,
end

theorem mod_two_geq_0
(x : ℝ)
: mod_two x ≥ 0
:= begin
  calc x - 2 * ↑⌊x / 2⌋
      ≥ x - 2 * (x / 2) : by { norm_num, exact floor_le (x / 2), }
  ... = 0               : by linarith
end

theorem mod_two_idempotent
(x : ℝ)
: mod_two (mod_two x) = mod_two x
:= bounding_id (mod_two x) (mod_two_le_2 x) (mod_two_geq_0 x)

theorem mod_two_addition
(a b : ℝ)
: mod_two ((mod_two a) + b) = mod_two (a+b)
:= begin
  unfold mod_two,
  calc a - 2 * ↑⌊a / 2⌋ + b - 2 * ↑⌊(a - 2 * ↑⌊a / 2⌋ + b) / 2⌋
      = a - 2 * ↑⌊a / 2⌋ + b - 2 * ↑⌊(a + b - 2 * ↑⌊a / 2⌋) / 2⌋ : by rw sub_add_eq_add_sub a (2 * ↑⌊a / 2⌋) b
  ... = a - 2 * ↑⌊a / 2⌋ + b - 2 * ↑⌊(a + b)/2 - (2 * ↑⌊a / 2⌋) / 2⌋ : by rw sub_div (a + b) (2 * ↑⌊a / 2⌋) 2
  ... = a - 2 * ↑⌊a / 2⌋ + b - 2 * ↑⌊(a + b)/2 - ↑⌊a / 2⌋⌋ : by {
    rw mul_comm (2:ℝ) (↑⌊a / 2⌋),
    have hhh : (∀(x y : ℝ), y ≠ 0 → (x*y)/y = x) := mul_div_cancel,
    rw hhh (↑⌊a / 2⌋) 2 two_ne_zero,
  }
  ... = a - 2 * ↑⌊a / 2⌋ + b - 2 * ↑(⌊(a + b)/2⌋ - ⌊a / 2⌋) : by rw floor_sub_int ((a + b)/2) ⌊a / 2⌋
  ... = a - 2 * ↑⌊a / 2⌋ + b - 2 * (↑(⌊(a + b)/2⌋) - ↑⌊a / 2⌋) : by rw int.cast_sub ⌊(a + b)/2⌋ ⌊a / 2⌋

  ... = a + b - 2 * ↑⌊(a + b) / 2⌋ : by linarith
end

theorem mod_two_subtraction
(a b : ℝ)
: mod_two (a-b) = mod_two ((mod_two a) - b)
:= begin
  rw sub_eq_add_neg a b,
  rw ←mod_two_addition,
  rw ←sub_eq_add_neg (mod_two a) b,
end

theorem mod_two_xsub_one_eq_mod_two_x_plus_one
(x : ℝ)
(h : mod_two x < 1)
: mod_two (x - 1) = (mod_two x) + 1
:= begin
  calc mod_two (x - 1)
      = mod_two (mod_two x - 1)     : mod_two_subtraction x 1
  ... = mod_two (mod_two x - 1 + 2) : by {rw mod_plus_two_eq_id (mod_two x - 1), }
  ... = mod_two (mod_two x + 1)     : by { ring, }
  ... = mod_two x + 1     : begin
    refine bounding_id (mod_two x + 1) _ _,
    linarith,
    linarith [mod_two_geq_0 x],
  end
end

theorem abs_of_mod_two_sub_mod_to_of_sub_one_eq_one
(x : ℝ)
: abs (mod_two x - mod_two (x - 1)) = 1
:= begin
  cases decidable.em (mod_two x ≥ 1) with mod_two_x_ge_1 ne_mod_two_x_ge_1, by {
    rw mod_two_subtraction x 1,
    have in_bounded_u : (mod_two x) - 1 < 2 := begin
      have := mod_two_le_2 x,
      linarith,
    end,

    have in_bounded_l : 0 ≤ (mod_two x) - 1, by linarith,
    rw bounding_id (mod_two x - 1) in_bounded_u in_bounded_l,
    calc abs (mod_two x - (mod_two x - 1))
        = abs 1 : by { refine congr rfl _, linarith, }
    ... = 1 : abs_one,
  },
  {
    have mod_x_le_1: mod_two x < 1 := not_le.mp ne_mod_two_x_ge_1,
    rw mod_two_xsub_one_eq_mod_two_x_plus_one x mod_x_le_1,


    calc abs (mod_two x - (mod_two x + 1))
        = abs (-1) : by { refine congr rfl _, linarith, }
    ... = abs 1 : abs_neg 1
    ... = 1 : abs_one,
  }
end

theorem bounding_mod_two
(a : ℝ)
(au : a < 2)
(al : 0 ≤ a)
(ha : mod_two a < 1)
: a < 1
:= begin
  rw (bounding_id a au al) at ha,
  exact ha,
end
