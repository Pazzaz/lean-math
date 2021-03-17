import algebra.continued_fractions
import data.real.basic
import algebra.continued_fractions.convergents_equiv
import tactic.unfold_cases

open generalized_continued_fraction as gcf

-- 1. Skriv ut theorem för \R
--     1. använd convergents'


-- `sum_prod a_k n` = ∑_{i=1}^{n} (∏_{j=1}^{i} a_j)
def sum_prod {K : Type*} [semiring K] (A : seq K) (n : ℕ) : K := ((list.range n).map (λ (i : ℕ), (A.take (i+1)).prod ) ).sum


theorem cons_take_eq_take_cons
{X : Type*}
(a : X)
(A : seq X)
(i : ℕ)
: (A.cons a).take (i+1) = (A.take i).cons a
:= begin
	unfold seq.take,
	rw seq.destruct_cons a,
	have hue : seq.take._match_1 (seq.take i) (some (a, A)) = list.cons a (seq.take i A) := rfl,
	rw hue,
end




/-
  Extract the first value from a sum of products
  Σ_{i=0}^{A.length-1} Π_{j=0}^{i} A.nth j
-/
theorem sum_prod_list_tail
{K : Type*} [semiring K]
(a : K)
(A : list K)
: ((list.range (a :: A).length).map (λ (i : ℕ), ((a :: A).take (i+1)).prod ) ).sum = a + a * ((list.range A.length).map (λ (i : ℕ), (A.take (i+1)).prod )).sum
:= begin
	let f := (λ i, (A.take i).prod ),
	calc  ((list.range (a :: A).length).map (λ i, ((a :: A).take (i+1)).prod ) ).sum
      = ((list.range (a :: A).length).map (λ i, a * f i ) ).sum                     : by finish
  ... = a * ((list.range (a :: A).length).map f ).sum                               : list.sum_map_mul_left (list.range (a :: A).length) f a
  ... = a * ((list.range (A.length + 1) ).map f ).sum                               : rfl
	... = a * ((list.cons 0 ((list.range A.length).map (nat.succ))).map f).sum        : by rw list.range_succ_eq_map A.length
	... = a * (list.cons (f 0) (((list.range A.length).map (nat.succ)).map f)).sum    : rfl
	... = a * (list.cons (f 0) ((list.range A.length).map (λ i, f (i+1) ))).sum       : by rw list.map_map f nat.succ (list.range A.length)
	... = a * (list.cons 1 ((list.range A.length).map (λ i, f (i+1) ))).sum           : rfl
	... = a*1 + a*(((list.range A.length).map (λ i, f (i+1) ))).sum                   : by { rw list.sum_cons, exact mul_add a 1 _}
	... = a   + a*(((list.range A.length).map (λ i, f (i+1) ))).sum                   : by rw mul_one a
end

theorem sum_prod_tail
{K : Type*} [semiring  K]
(A : seq K)
(a : K)
(n : ℕ)
: sum_prod (seq.cons a A) (n+1) = a + a * sum_prod A n
:= begin
	let f := (λ i, (A.take i).prod ),
	calc sum_prod (A.cons a) (n+1)
		= ((list.range (n+1)).map (λ i, ((A.cons a).take (i+1)).prod ) ).sum    : rfl
	... = ((list.range (n+1)).map (λ i, ((A.take i).cons a).prod ) ).sum        : by {  congr,
																						refine funext _,
																						intro nn,
																						exact congr rfl (cons_take_eq_take_cons a A nn), }
	... = ((list.range (n+1)).map (λ i, a * f i)).sum                           : by {  congr,
																						refine funext _,
																						intro _,
																						exact list.prod_cons, }
	... = a * ((list.range (n+1)).map f).sum                                    : list.sum_map_mul_left (list.range (n+1)) f a
	... = a * ((list.cons 0 ((list.range n).map (nat.succ))).map f).sum         : by rw list.range_succ_eq_map n
	... = a * (list.cons (f 0) (((list.range n).map (nat.succ)).map f) ).sum    : rfl
	... = a * (list.cons (f 0) (((list.range n)).map (λ i, f (i+1) )) ).sum     : by rw (list.map_map f nat.succ (list.range n))
	... = a * (list.cons 1 (((list.range n)).map (λ i, f (i+1) )) ).sum         : rfl
	... = a * (1 + (((list.range n)).map (λ i, f (i+1) ) ).sum)                 : by rw list.sum_cons
	... = a*1 + (a * (((list.range n)).map (λ i, f (i+1) ) ).sum)               : mul_add a 1 ((list.range n).map (λ i, (A.take (i+1)).prod)).sum
	... = a +   (a * (((list.range n)).map (λ i, f (i+1) ) ).sum)               : by rw mul_one a
end



def simple_part
{X : Type*} [division_ring X]
(A : seq X)
: gcf X
:= ⟨0, A.map (λ ai, ⟨-ai, 1 + ai⟩ )⟩

@[simp]
theorem simple_part_h
{X : Type*} [division_ring X]
(A : seq X)
: (simple_part A).h = 0
:= rfl

@[simp]
theorem simple_part_s
{X : Type*} [division_ring X]
(A : seq X)
: (simple_part A).s = A.map (λ ai, ⟨-ai, 1 + ai⟩ )
:= rfl

def gcf_cons
{X : Type*}
(p : gcf.pair X)
(A : gcf X)
: gcf X := ⟨A.h, seq.cons p A.s⟩

theorem gcf_cons_def
{X : Type*}
(p : gcf.pair X)
(A : gcf X)
: gcf_cons p A = ⟨A.h, seq.cons p A.s⟩
:= rfl

@[simp]
theorem gcf_cons_ignore_int
{X : Type*}
(p : gcf.pair X)
(A : gcf X)
: (gcf_cons p A).h = A.h
:= rfl

@[simp]
theorem gcf_cons_eq_seq_cons
{X : Type*}
(p : gcf.pair X)
(A : gcf X)
: (gcf_cons p A).s = seq.cons p A.s
:= rfl

-- TODO: Är det här rätt definition? Vad händer om det är en väldigt kort sekvens?
-- ⟨a0, 1⟩ ⟨-a1, 1+a1⟩ ⟨-a2, 1+a2⟩...
def rhs_euler
{X : Type*} [division_ring X]
(A : seq X) : gcf X
:= begin
	let splitted := seq.split_at 1 A,
	let head     := splitted.1.map (λ (a0 : X), gcf.pair.mk a0 1),
	let head_seq := seq.of_list head,
	let tail     := splitted.2.map (λ (ai : X), gcf.pair.mk (-ai) (1+ai)),
	let joined   := seq.append head_seq tail,
	exact ⟨0,joined⟩,
end

-- def map_head
-- {X Y : Type*}
-- (f_head f : X → Y)
-- (A : seq X)
-- : seq Y
-- := seq.zip_with (λ(n : ℕ) (x : X), ite (n = 0) (f_head x) (f x)) seq.nats A

/- Apply one function to the head of the list and one function to the rest-/
def map_head
{X Y : Type*}
(f_head f : X → Y)
(A : seq X)
: seq Y
:= option.get_or_else (option.map ((λ (a : seq1 X), seq1.to_seq ((f_head a.1, a.2.map f)))) (seq.destruct A)) seq.nil

theorem option_get_or_else_dist
{X Y: Type*}
(e : X)
(t : option X)
(f : X → Y)
: f (option.get_or_else t e) = option.get_or_else (t.map f) (f e)
:= begin
  cases t,
  rw option.map_none',
  exact rfl,
  simp only [option.get_or_else_some, option.map_some', eq_self_iff_true],
end

theorem seq_1_to_seq_tail
{X : Type*}
(a : X)
(A : seq X)
: (seq1.to_seq (a, A)).tail = A
:= seq.tail_cons a A

@[simp]
theorem map_head_tail_eq_map'
{X Y : Type*}
(f_head f : X → Y)
(A : seq X)
: (map_head f_head f A).tail = A.tail.map f
:= begin
  unfold map_head,
  rw option_get_or_else_dist seq.nil _ seq.tail,
  simp only [option.map_map, seq.map_tail, seq.tail_nil],
  rw function.comp,
  conv in (λ (a : seq1 X), (seq1.to_seq (f_head a.fst, seq.map f a.snd)).tail)
  { funext, rw seq_1_to_seq_tail _ _, skip, },
  classical,
  cases decidable.em (A.destruct = none) with hn hs,
  { rw hn,
    rw seq.destruct_eq_nil hn,
    simp only [seq.map_nil, seq.tail_nil, option.map_none'],
    exact rfl, },
  { have a_tail_zero_some : ↥(option.is_some (A.destruct)) := option.ne_none_iff_is_some.mp hs,
    let dest := option.get a_tail_zero_some,
    have A_destruct_eq_some_dest : A.destruct = some dest := (option.some_get a_tail_zero_some).symm,
    rw A_destruct_eq_some_dest,
    have huehue : option.map (λ (a : seq1 X), seq.map f a.snd) (some dest) = some ((λ (a : seq1 X), seq.map f a.snd) dest) := rfl,
    rw huehue,
    simp,
    have A_destruct_split : A.destruct = some (dest.1, dest.2) := by {rw A_destruct_eq_some_dest, refine congr rfl _, exact prod.ext rfl rfl},
    have A_tail_eq_dest := congr_arg seq.tail (seq.destruct_eq_cons A_destruct_split),
    simp at A_tail_eq_dest,
    rw A_tail_eq_dest.symm,
    exact seq.map_tail f A, }
end

@[simp]
theorem map_head_head_eq_map'
{X Y : Type*}
(f_head f : X → Y)
(A : seq X)
: (map_head f_head f A).head = A.head.map f_head
:= begin
  unfold map_head,
  rw option_get_or_else_dist seq.nil _ seq.head,
  simp,
  sorry,
end


/-- Extracts the first term of a continued fraction -/
@[simp]
theorem cons_convergents'_eq_div_plus_convergents'
{K : Type*} [division_ring K]
(a b : K)
(A : gcf K)
{h : A.h = 0}
(n : ℕ)
: (gcf_cons (gcf.pair.mk a b) A).convergents' (n+1) = (a / (b + A.convergents' n))
:= begin
	unfold gcf_cons at *,
	unfold gcf.convergents' at *,
	rw h,
	simp,
	unfold gcf.convergents'_aux,
	simp,
	unfold gcf.convergents'_aux._match_1,
end


@[simp]
theorem nilling
(X : Type*)
: seq.split_at 1 seq.nil = ⟨[], (seq.nil : seq X)⟩
:= rfl

theorem split_at_one_cons_snd_eq_id
{X : Type*} [division_ring X]
(A : seq X)
(a : X)
: (seq.split_at 1 (seq.cons a A)).snd = A
:= begin
	unfold seq.split_at,
	rw seq.destruct_cons,
	exact rfl,
end

theorem split_at_one_cons_fst_eq_cons
{X : Type*} [division_ring X]
(A : seq X)
(a : X)
: (seq.split_at 1 (seq.cons a A)).fst = [a]
:= begin
	unfold seq.split_at,
	rw seq.destruct_cons,
	exact rfl,
end

theorem rhs_euler_eq
{X : Type*} [division_ring X]
(A : seq X)
(a : X)
(n : ℕ)
: (rhs_euler (seq.cons a A)).convergents' n.succ = a / ( 1 + (simple_part A).convergents' n)
:= begin
	rw ←cons_convergents'_eq_div_plus_convergents',
	rw gcf_cons_def,
	congr,
	unfold rhs_euler,
	simp only [],
	split,
	exact rfl,
	rw simple_part_s,
	rw split_at_one_cons_snd_eq_id,
	rw split_at_one_cons_fst_eq_cons,
	simp,
	exact simple_part_h A,
end


theorem rhs_euler_nil
{X : Type*} [division_ring X]
: rhs_euler (seq.nil : seq X) = ⟨0, seq.nil⟩
:= begin
	unfold rhs_euler,
	simp only [seq.append_nil, list.map_nil, nilling, eq_self_iff_true, seq.map_nil, and_self, seq.of_list_nil],
end

@[simp]
theorem seq_map_head
{A B : Type*}
(S : seq A)
(f : A → B)
(nth_zero_some:  (↥((S.nth 0).is_some) : Prop))
: option.map f S.head = some (f (option.get nth_zero_some))
:= begin
	have nth_zero_eq_head : S.nth 0 = S.head := rfl,
	rw nth_zero_eq_head at nth_zero_some,
	have dkkdk  : S.head = some (option.get nth_zero_some) := by norm_num,
	have duedue : option.map f (some (option.get nth_zero_some)) = some (f (option.get nth_zero_some)) := rfl,
	rw dkkdk,
	exact duedue,
end

theorem sub_div_suc_ne_sub_one
{X : Type*} [division_ring X] (a : X)
: -a / (1 + a) ≠ -1 := begin
	classical,
	rw neg_div (1 + a) a,
	refine function.injective.ne neg_injective _,
	by_contra h,
	simp only [not_not, ne.def] at h,
	have gkgk : a - a = 1 + a - a := congr (congr_arg has_sub.sub (eq_of_div_eq_one h)) rfl,
	rw [add_sub_assoc 1 a a, sub_self a, add_zero (1 : X)] at gkgk,
	exact zero_ne_one gkgk,
end

theorem jdjdjd
{X : Type*} [division_ring X]
: (0 : X) ≠ 1
:= zero_ne_one

theorem hueheeuh2
{X : Type*} [division_ring X]
(a b : X)
: a ≠ b → -a ≠ -b
:= begin
	intro k,
	exact function.injective.ne neg_injective k,
end


theorem add_to_denom_of_succ_ne_sub_one
{X : Type*} [division_ring X]
(a b : X)
(h : b ≠ -1)
: -a / (1 + a + b) ≠ -1
:= begin
	rw neg_div (1 + a + b) a,
	apply hueheeuh2,
	classical,
	cases decidable.em ((1 + a + b) = 0),
	rw [h_1, div_zero a],
	exact zero_ne_one,
	by_contradiction wack,
	rw not_not at wack,
	have huehu := (div_eq_one_iff_eq h_1).mp wack,
	rw [add_comm 1 a, add_assoc a 1 b] at huehu,
	have nexter : (1 + b) = 0 := self_eq_add_right.mp huehu,
	rw [add_comm 1 b, ←sub_neg_eq_add b 1] at nexter,
	exact h (sub_eq_zero.mp nexter),
end



--theorem rhs_euler_eq

theorem simple_convergents_ne_sub_one
{X : Type*} [division_ring X]
(A : seq X)
(n : ℕ)
(h_in : A.nth n ≠ none)
: (simple_part A).convergents' n ≠ -1
:= begin
	induction n with h hd generalizing A,
	{ unfold simple_part,
		simp only [ gcf.zeroth_convergent'_eq_h,
					ne.def,
					not_false_iff,
					one_ne_zero,
					zero_eq_neg ], },
	{ have a_zero_some : ↥(option.is_some (A.nth 0)) := option.ne_none_iff_is_some.mp (mt (seq.le_stable A bot_le) h_in),
		let a0 := option.get a_zero_some,
		have cons_adder := seq.destruct_eq_cons (seq_map_head A (λ a', (a', A.tail)) a_zero_some),
		unfold simple_part,
		rw cons_adder,
		simp only [seq.map_tail, seq.map_cons],
		let f := (λ (ai : X), gcf.pair.mk (-ai) (1 + ai)),
		let thing : gcf X := ⟨0, (seq.map f A).tail⟩,
		rw ←gcf_cons_def (gcf.pair.mk (-a0) (1 + a0)) thing,
		have kkkk: thing.h = 0 := rfl,
		rw @cons_convergents'_eq_div_plus_convergents' _ _ _ _ _ kkkk _,
		have back_again : thing = simple_part A.tail := by { unfold simple_part, rw (seq.map_tail f A), },
		rw back_again,
		have A_tail_nth_ne_none : A.tail.nth h ≠ none := by {rw (seq.nth_tail A h), exact h_in},
		exact add_to_denom_of_succ_ne_sub_one a0 ((simple_part A.tail).convergents' h) (hd A.tail A_tail_nth_ne_none), }
end

-- gcf.convergents'_aux._match_1 0 (seq.map (λ (ai : ℝ), {a := -ai, b := 1 + ai}) A).head

#check gcf.convergents'_aux._match_1

theorem seq_map_eq_list_map
(X Y : Type*) [division_ring X]
(f : X -> Y)
(A : seq ( gcf.pair X))
(n : ℕ)
(h1 : (A.nth 0) ≠ none )
(h2 : (A.nth 1) ≠ none )
: gcf.convergents'_aux A 1 = (option.get (option.ne_none_iff_is_some.mp h1)).a / (option.get (option.ne_none_iff_is_some.mp h1)).b
:= sorry
-- theorem test1
-- (a b : Prop)
-- : (a -> b) -> (¬b -> ¬a)
-- := begin
--     library_search,
-- end

-- theorem euler_b
-- (A : seq ℝ)
-- (n : ℕ)
-- (h : A.nth n ≠ none)
-- :  ≠ -1
-- := begin
--     induction n with h hd,
--     unfold rhs_euler,
--     simp,
--     induction h with h2 hd2,
--     unfold rhs_euler,
--     simp,

-- end

-- The rhs has a singularity at x = -1 -a. If it was set to 0 at that point, both sides would be equal then x ≠ -1
theorem move_divs
{X : Type*} [division_ring X]
(a x : X)
(h1 : x ≠ -1)
(h2 : x ≠ -1 - a)
: (1 / (1 + (-a / (1 + a + x)))) = 1 + (a / (1 + x))
:= begin
	classical,
	have yepp : (1 + a + x) ≠ 0 := begin
		by_contradiction,
		rw not_not at h,
		have mumu: x = -(1+a) := (neg_eq_of_add_eq_zero h).symm,
		rw neg_add' 1 a at mumu,
		exact h1 (absurd mumu h2),
	end,
	have yepp2 : 1 + x ≠ 0 := begin
		by_contradiction,
		rw not_not at h,
		have mumu: x = -1 := (neg_eq_of_add_eq_zero h).symm,
		exact h1 mumu,
	end,
	calc 1 / (1 + (-a / (1 + a + x)))
		= 1 / ((1 + a + x)/(1 + a + x) + (-a / (1 + a + x))) : by {congr, exact (div_self yepp).symm,}
	... = 1 / ((1 + a + x + -a) / (1 + a + x))             : by rw div_add_div_same (1 + a + x) (-a) (1 + a + x)
	... = 1 / ((1 + a + -a + x) / (1 + a + x))             : by rw add_right_comm (1 + a) x (-a)
	... = 1 / ((1 + x) / (1 + a + x))                      : by rw add_neg_eq_of_eq_add rfl
	... = (1 + a + x) / (1 + x)                            : one_div_div (1 + x) (1 + a + x)
	... = (1 + x + a) / (1 + x)                            : by rw add_right_comm 1 x a
	... = ((1 + x) / (1 + x)) + (a / (1 + x))              : add_div (1 + x) a (1 + x)
	... = 1 + (a / (1 + x))                                : by rw div_self yepp2
end


/-
This is **Euler's Continued Fraction Formula**.
We have `h2` to avoid division in the continued fraction. These are normally
ignored. If you treat the continued fraction as a function then it can be
extended to ignore the singularities. These issues can't be ignored when
formalizing.
-/

theorem euler_cff
{X : Type*} [division_ring X]
(A : seq X)
(n : ℕ)
(h : A.nth n ≠ none)
(h2 : ∀ n1, n1 < n → 1 ≤ n1 → some ((simple_part (A.drop n1.succ)).convergents' (n-(n1.succ))) ≠ (A.nth n1).map (λ an1, -(1 + an1)) )
: sum_prod A n = (rhs_euler A).convergents' n
:= begin
	induction n with hi hdi generalizing A,
	{ unfold sum_prod,
		unfold rhs_euler,
		simp only [ list.sum_nil,
					nat.nat_zero_eq_zero,
					list.map_nil,
					eq_self_iff_true,
					gcf.zeroth_convergent'_eq_h,
					list.range_zero ], },
	{ have A_tail_nth_ne_none      : A.tail.nth hi ≠ none             := by { rw seq.nth_tail A hi, exact h, },
		have A_tail_nth_zero_ne_none : A.tail.nth 0 ≠ none              := mt (seq.le_stable A.tail (bot_le)) A_tail_nth_ne_none,
		have a_tail_zero_some        : ↥(option.is_some (A.tail.nth 0)) := option.ne_none_iff_is_some.mp A_tail_nth_zero_ne_none,
		have thingy3                 : A.nth 0 ≠ none                   := mt (seq.le_stable A (bot_le)) h,
		have a_zero_some             : ↥(option.is_some (A.nth 0))      := option.ne_none_iff_is_some.mp thingy3,
		have cons_adder                                                 := seq.destruct_eq_cons (seq_map_head A (λ a', (a', A.tail)) a_zero_some),
		set a0 := option.get a_zero_some,
		set a1 := option.get a_tail_zero_some,
		induction hi with hi hi2,
		{
			unfold sum_prod,
			unfold rhs_euler,
			have yepp: list.range 1 = [0] := rfl,
			rw yepp,
			simp,
			rw cons_adder,
			rw split_at_one_cons_fst_eq_cons,
			rw split_at_one_cons_snd_eq_id,
			have yepping : seq.take 1 (seq.cons a0 A.tail) = [a0] := begin
				rw cons_take_eq_take_cons a0 A.tail 0,
				simp only [true_and, eq_self_iff_true],
				exact rfl,
			end,
			rw yepping,
			simp only [ seq.nil_append,
						mul_one,
						list.map.equations._eqn_2,
						seq.map_tail,
						seq.cons_append,
						list.map_nil,
						list.prod_cons,
						list.prod_nil,
						seq.of_list_nil,
						seq.of_list_cons    ],
			rw ←gcf_cons_def ⟨a0, 1⟩ ⟨0, (seq.map (λ (ai : X), gcf.pair.mk (-ai) (1 + ai)) A).tail⟩,
			rw cons_convergents'_eq_div_plus_convergents' _ _ _,
			simp only [add_zero, eq_self_iff_true, generalized_continued_fraction.zeroth_convergent'_eq_h, div_one],
		},
		{

			have cons_adder_two : A.tail = (seq.cons a1 A.tail.tail) := seq.destruct_eq_cons (seq_map_head A.tail (λ a', (a', A.tail.tail)) a_tail_zero_some),

			have gotem := hdi A.tail A_tail_nth_ne_none _,

			have fkfkfk : A.tail.tail.nth hi ≠ none := by {rw seq.nth_tail _ _, exact A_tail_nth_ne_none,},

			calc sum_prod A hi.succ.succ
				= sum_prod (A.tail.cons a0) hi.succ.succ                                          : by nth_rewrite 0 cons_adder
			... = a0 + a0 * sum_prod A.tail hi.succ                                             : sum_prod_tail (A.tail) a0 hi.succ
			... = a0 + a0 * ((rhs_euler A.tail).convergents' hi.succ)                           : by rw gotem
			... = a0 * 1 + a0 * ((rhs_euler A.tail).convergents' hi.succ)                       : by rw mul_one a0
			... = a0 * (1 + ((rhs_euler A.tail).convergents' hi.succ))                          : by rw (mul_add a0 1 _).symm
			... = a0 * (1 + ((rhs_euler (seq.cons a1 A.tail.tail)).convergents' hi.succ))       : by {  congr,  exact cons_adder_two, }
			... = a0 * (1 + (a1 / ( 1 + (simple_part A.tail.tail).convergents' hi)))            : by {  congr, exact (rhs_euler_eq A.tail.tail a1 hi),}
			... = a0 * (1 /(1 + (-a1 / ( 1 + a1 + (simple_part A.tail.tail).convergents' hi)))) : by {  congr,
                                                                                                  have kdkdkdk := (move_divs a1 ((simple_part A.tail.tail).convergents' hi) _ _).symm,
                                                                                                  exact kdkdkdk,
                                                                                                  have kkkkk := simple_convergents_ne_sub_one A.tail.tail hi,
                                                                                                  exact kkkkk fkfkfk,
                                                                                                  simp only [ nat.succ_sub_succ_eq_sub,
                                                                                                              seq.drop.equations._eqn_1,
                                                                                                              ne.def,
                                                                                                              nat.sub_zero,
                                                                                                              seq.drop.equations._eqn_2],
                                                                                                  have from_hyp : some ((simple_part A.tail.tail).convergents' hi) ≠ option.map (λ (an1 : X), -(1 + an1)) (A.nth 1) := h2 1 _ rfl.ge,
                                                                                                  have to_tail: (A.nth 1) = A.tail.nth 0 := (seq.nth_tail A 0).symm,
                                                                                                  have a1er : option.get a_tail_zero_some = a1 := rfl,
                                                                                                  rw [  to_tail,
                                                                                                        (option.some_get a_tail_zero_some).symm,
                                                                                                        a1er,
                                                                                                        option.map_some',
                                                                                                        neg_add] at from_hyp,
                                                                                                  apply ne_of_apply_ne some,
                                                                                                  rw (sub_eq_add_neg (-1) a1).symm at from_hyp,
                                                                                                  exact from_hyp,
                                                                                                  exact (cmp_eq_lt_iff 1 (nat.succ hi).succ).mp rfl, }
			... = a0 * (1 / (1 + (simple_part A.tail).convergents' hi.succ))                    : by {  congr,
                                                                                                  have kdkdkd := (cons_convergents'_eq_div_plus_convergents' (-a1) (1 + a1) (simple_part A.tail.tail) hi).symm,
                                                                                                  unfold simple_part at kdkdkd,
                                                                                                  rw gcf_cons_def _ _ at kdkdkd,
                                                                                                  simp at kdkdkd,
                                                                                                  set f := (λ (ai : X), (⟨-ai, 1 + ai⟩  : gcf.pair X)),
                                                                                                  have bring_in_tail := eq.symm (seq.map_tail f A),
                                                                                                  rw (seq.map_tail f A     ).symm at kdkdkd,
                                                                                                  rw (seq.map_tail f A.tail).symm at kdkdkd,
                                                                                                  rw (seq.map_cons f a1 A.tail.tail).symm at kdkdkd,
                                                                                                  rw cons_adder_two.symm at kdkdkd,
                                                                                                  exact kdkdkd,
                                                                                                  exact rfl, }
			... = (a0*1) / (1 + (simple_part A.tail).convergents' hi.succ)                      : by rw mul_div_assoc' a0 1 _
			... = a0 / (1 + (simple_part A.tail).convergents' hi.succ)                          : by rw mul_one a0
			... = (rhs_euler (seq.cons a0 A.tail)).convergents' hi.succ.succ                    : (rhs_euler_eq A.tail a0 hi.succ).symm
			... = (rhs_euler A).convergents' hi.succ.succ                                       : by rw eq.symm cons_adder,
			{ intros nn nn_lt_hi_succ nn_le_one,
        have fone : nn + 1 < hi.succ.succ := nat.lt_succ_iff.mpr nn_lt_hi_succ,
        have ftwo : 1 ≤ nn + 1 := nat.lt.step nn_le_one,
        have nicer := h2 (nn + 1) fone ftwo,
        rw (seq.dropn_tail A (nn+1)).symm at nicer,
        have kdkdkdk : hi.succ.succ - (nn + 1).succ = hi.succ - nn.succ := by norm_num,
        rw kdkdkdk at nicer,
        rw (seq.nth_tail A nn).symm at nicer,
        exact nicer,  } },},

end

def map_head_list
{X Y: Type*}
(f_head f : X → Y)
(A : list X)
: list Y
:= A.map_with_index (λ i x, ite (i = 0) (f_head x) (f x))

@[simp]
theorem map_head_list_tail_eq_map
{X Y : Type*}
(f_head f : X → Y)
(A : list X)
: (map_head_list f_head f A).tail = A.tail.map f
:= sorry


theorem euler_cff_list
{X : Type*} [division_ring X]
(A : list X)
(h2 : ∀ n1 (h : n1 < A.length), 1 ≤ n1
  → ((⟨0, (A.drop n1.succ).map (λ (ai : X), gcf.pair.mk (-ai) (1+ai)) ⟩ : gcf X ).convergents' (A.length-(n1.succ)))
      ≠ (λ (an1 : X), -(1 + an1)) (A.nth_le n1 h))
: ((list.range A.length).map (λ (i : ℕ), (A.take (i+1)).prod ) ).sum = (⟨0, (map_head_list (λ (a0 : X), gcf.pair.mk a0 1) (λ ai, gcf.pair.mk (-ai) (1 + ai) ) A)⟩ : gcf X ).convergents' A.length
:= sorry

-- This should be the easiest to work with. Most lists are longer than 1.
-- TODO: Should you just have a hypothesis of `0 < A.length`?
theorem euler_cff_list_cons
{X : Type*} [division_ring X]
(A : list X)
(a : X)
(h2 : ∀ n1 (h : n1 < (a :: A).length), 1 ≤ n1
  → ((⟨0, ((a :: A).drop n1.succ).map (λ (ai : X), gcf.pair.mk (-ai) (1+ai)) ⟩ : gcf X ).convergents' ((a :: A).length-(n1.succ)))
      ≠ (λ (an1 : X), -(1 + an1)) ((a :: A).nth_le n1 h))
: ((list.range (a :: A).length).map (λ (i : ℕ), ((a :: A).take (i+1)).prod ) ).sum = (⟨0, (list.cons (gcf.pair.mk a 1) (A.map (λ ai, gcf.pair.mk (-ai) (1 + ai) )))⟩ : gcf X ).convergents' (a :: A).length
:= sorry

theorem dkdkdk
(X : Type*)
(hi : ℕ)
(nn : ℕ)
(A : seq X)
: A.nth (nn + 1) = A.tail.nth nn
:= by { refine eq.symm _, exact seq.nth_tail A nn}

-- theorem hueheuhe
-- (a : ℝ)
-- : (1 / (1 / a)) = a
-- := one_div_one_div a,

-- 2. Skriv ut de olika delarna av induktionbeviset och bevisa dem
--     1. Bevisa "bla bla \neq -1" som ett separat lemma, fortfarande med induktion.
--     2. Bevisa det vi bryr oss om.
-- 3. Sätt ihop dem.
--     1. Man kanske kommer behöva göra något smart för att visa att det gäller i det oändliga fallet
-- 4. Generalisera till komplexa tal.
-- 5. Generalisera till något annat?