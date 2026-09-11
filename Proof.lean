import Mathlib

/-!
# An explicit Heisenberg-group counterexample for Kourovka 21.106

This file supplies the declarations expected by the statement file in the
request.  The formula is actual, parameter-free Mathlib first-order syntax.
Its free-variable support is checked, and its semantics is proved below.

The source contains complete proof attempts and no admitted lemmas or new
axiom declarations.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

universe u

namespace Kourovka21106

/-- Our commutator convention, expanded into pure group operations. -/
def groupComm {G : Type u} [Group G] (a b : G) : G :=
  a * b * a⁻¹ * b⁻¹

/-! ## Genuine first-order syntax, kept separate from the caller's language -/

namespace InternalSyntax

inductive FunctionSymbol : ℕ → Type
  | one : FunctionSymbol 0
  | inv : FunctionSymbol 1
  | mul : FunctionSymbol 2

def language : FirstOrder.Language where
  Functions := FunctionSymbol
  Relations := fun _ => Empty

instance structureOfGroup (G : Type u) [Group G] : language.Structure G where
  funMap := fun {_} f =>
    match f with
    | .one => fun _ => (1 : G)
    | .inv => fun xs => (xs 0)⁻¹
    | .mul => fun xs => xs 0 * xs 1
  RelMap := fun {_} r _ => nomatch r

abbrev BT (n : ℕ) := language.Term (Fin 1 ⊕ Fin n)
abbrev BF (n : ℕ) := language.BoundedFormula (Fin 1) n

def freeX {n : ℕ} : BT n := FirstOrder.Language.var (Sum.inl 0)
def bound {n : ℕ} (i : Fin n) : BT n :=
  FirstOrder.Language.var (Sum.inr i)

def oneTerm {n : ℕ} : BT n :=
  FirstOrder.Language.func FunctionSymbol.one Fin.elim0

def invTerm {n : ℕ} (s : BT n) : BT n :=
  FirstOrder.Language.func FunctionSymbol.inv ![s]

def mulTerm {n : ℕ} (s t : BT n) : BT n :=
  FirstOrder.Language.func FunctionSymbol.mul ![s, t]

def commTerm {n : ℕ} (s t : BT n) : BT n :=
  mulTerm (mulTerm (mulTerm s t) (invTerm s)) (invTerm t)

/-- Bound variables: a=0, b=1, y=2, c=3, d=4. -/
def witnessBody : BF 5 :=
  ((commTerm (bound 0) (bound 3)).bdEqual (bound 2)) ⊓
    (((commTerm (bound 1) (bound 3)).bdEqual oneTerm) ⊓
      (((commTerm (bound 1) (bound 4)).bdEqual (bound 2)) ⊓
        ((commTerm (bound 0) (bound 4)).bdEqual oneTerm)))

/-- At depth 3, this says that y commutes with every element t. -/
def centralY : BF 3 :=
  ((mulTerm (bound (2 : Fin 4)) (bound 3)).bdEqual
    (mulTerm (bound 3) (bound 2))).all

/--
∃ a b, [a,b] = x ∧
  ∀ y, (∀ t, y*t = t*y) →
    ∃ c d, [a,c] = y ∧ [b,c] = 1 ∧ [b,d] = y ∧ [a,d] = 1.

Quantification appends bound variables (Mathlib's de Bruijn levels).
-/
def rawFormula : language.Formula (Fin 1) :=
  (((commTerm (bound (0 : Fin 2)) (bound 1)).bdEqual freeX) ⊓
    ((centralY.imp witnessBody.ex.ex).all)).ex.ex

end InternalSyntax

/-- Pure first-order formulas whose free-variable support is exactly `Fin n`. -/
abbrev Formula (n : ℕ) : Type :=
  { φ : InternalSyntax.language.Formula (Fin n) //
      φ.freeVarFinset = Finset.univ }

/-- The solution set under the canonical interpretation of group operations. -/
def values {G : Type u} [Group G] (φ : Formula 1) : Set G :=
  { x : G | φ.val.Realize (fun _ : Fin 1 => x) }

/-- No element of any group is used as a parameter in this formula. -/
def counterexampleFormula : Formula 1 :=
  ⟨InternalSyntax.rawFormula, by decide⟩

/-- A readable version of the formula's semantics, not a replacement syntax. -/
def CounterexamplePredicate {G : Type u} [Group G] (x : G) : Prop :=
  ∃ a b : G, groupComm a b = x ∧
    ∀ y : G, (∀ t : G, y * t = t * y) →
      ∃ c d : G,
        groupComm a c = y ∧ groupComm b c = 1 ∧
          groupComm b d = y ∧ groupComm a d = 1

/-- The syntactic formula has precisely the advertised semantics. -/
theorem mem_values_iff {G : Type u} [Group G] (x : G) :
    x ∈ values (G := G) counterexampleFormula ↔ CounterexamplePredicate x := by
  classical
  change InternalSyntax.rawFormula.Realize (fun _ : Fin 1 => x) ↔ _
  simp only [FirstOrder.Language.Formula.Realize,
    InternalSyntax.rawFormula, InternalSyntax.centralY, InternalSyntax.witnessBody,
    FirstOrder.Language.BoundedFormula.realize_ex,
    FirstOrder.Language.BoundedFormula.realize_inf,
    FirstOrder.Language.BoundedFormula.realize_all,
    FirstOrder.Language.BoundedFormula.realize_imp,
    FirstOrder.Language.BoundedFormula.realize_bdEqual] <;> rfl

/-! ## The Heisenberg group, explicitly constructed in every universe -/

/-- Three small coordinates, with a universe-polymorphic carrier. -/
@[ext]
structure Heis (R : Type) : Type u where
  x : R
  y : R
  z : R

namespace Heis

variable {R : Type}

def multiply [CommRing R] (a b : Heis.{u} R) : Heis.{u} R :=
  ⟨a.x + b.x, a.y + b.y, a.z + b.z + a.x * b.y⟩

def identity [CommRing R] : Heis.{u} R := ⟨0, 0, 0⟩

def inverse [CommRing R] (a : Heis.{u} R) : Heis.{u} R :=
  ⟨-a.x, -a.y, -a.z + a.x * a.y⟩

instance group [CommRing R] : Group (Heis.{u} R) where
  mul := multiply
  one := identity
  inv := inverse
  mul_assoc a b c := by
    change multiply (multiply a b) c = multiply a (multiply b c)
    apply Heis.ext <;> dsimp [multiply] <;> ring
  one_mul a := by
    change multiply identity a = a
    apply Heis.ext <;> dsimp [multiply, identity] <;> ring
  mul_one a := by
    change multiply a identity = a
    apply Heis.ext <;> dsimp [multiply, identity] <;> ring
  inv_mul_cancel a := by
    change multiply (inverse a) a = identity
    apply Heis.ext <;> dsimp [multiply, inverse, identity] <;> ring

@[simp] theorem mul_x [CommRing R] (a b : Heis.{u} R) :
    (a * b).x = a.x + b.x := rfl
@[simp] theorem mul_y [CommRing R] (a b : Heis.{u} R) :
    (a * b).y = a.y + b.y := rfl
@[simp] theorem mul_z [CommRing R] (a b : Heis.{u} R) :
    (a * b).z = a.z + b.z + a.x * b.y := rfl
@[simp] theorem one_x [CommRing R] : (1 : Heis.{u} R).x = 0 := rfl
@[simp] theorem one_y [CommRing R] : (1 : Heis.{u} R).y = 0 := rfl
@[simp] theorem one_z [CommRing R] : (1 : Heis.{u} R).z = 0 := rfl
@[simp] theorem inv_x [CommRing R] (a : Heis.{u} R) : (a⁻¹).x = -a.x := rfl
@[simp] theorem inv_y [CommRing R] (a : Heis.{u} R) : (a⁻¹).y = -a.y := rfl
@[simp] theorem inv_z [CommRing R] (a : Heis.{u} R) :
    (a⁻¹).z = -a.z + a.x * a.y := rfl

def central [CommRing R] (k : R) : Heis.{u} R := ⟨0, 0, k⟩

@[simp] theorem central_x [CommRing R] (k : R) :
    (central k : Heis.{u} R).x = 0 := rfl
@[simp] theorem central_y [CommRing R] (k : R) :
    (central k : Heis.{u} R).y = 0 := rfl
@[simp] theorem central_z [CommRing R] (k : R) :
    (central k : Heis.{u} R).z = k := rfl

@[simp] theorem central_mul [CommRing R] (k l : R) :
    (central k : Heis.{u} R) * central l = central (k + l) := by
  apply Heis.ext <;> simp [central]

theorem central_commutes [CommRing R] (k : R) (a : Heis.{u} R) :
    central k * a = a * central k := by
  apply Heis.ext <;> simp [central, add_comm]

def det [CommRing R] (a b : Heis.{u} R) : R :=
  a.x * b.y - b.x * a.y

theorem groupComm_eq [CommRing R] (a b : Heis.{u} R) :
    groupComm a b = central (det a b) := by
  apply Heis.ext <;>
    simp only [groupComm, mul_x, mul_y, mul_z, inv_x, inv_y, inv_z,
      central_x, central_y, central_z] <;>
    simp [det] <;> ring

/-- The two-dimensional determinant identity used in the finiteness proof. -/
theorem det_identity [CommRing R] (a b c d : Heis.{u} R) :
    det a b * det c d = det a c * det b d - det a d * det b c := by
  dsimp [det]
  ring

def coord (a : Heis.{u} R) (i : Fin 3) : R := ![a.x, a.y, a.z] i

instance finite [Finite R] : Finite (Heis.{u} R) :=
  Finite.of_injective (fun a : Heis.{u} R => (a.x, a.y, a.z)) (by
    intro a b hab
    apply Heis.ext
    · exact congrArg (fun t : R × R × R => t.1) hab
    · exact congrArg (fun t : R × R × R => t.2.1) hab
    · exact congrArg (fun t : R × R × R => t.2.2) hab)

end Heis

abbrev CounterexampleGroup : Type u := Heis.{u} ℤ

/-! ## Residual finiteness by coordinate reduction modulo n -/

def reduction (n : ℕ) : CounterexampleGroup.{u} →* Heis.{0} (ZMod n) where
  toFun a := ⟨(a.x : ZMod n), (a.y : ZMod n), (a.z : ZMod n)⟩
  map_one' := by
    apply Heis.ext <;> simp
  map_mul' a b := by
    apply Heis.ext <;> simp

theorem integer_separation (k : ℤ) (hk : k ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ (k : ZMod n) ≠ 0 := by
  refine ⟨k.natAbs + 1, by omega, ?_⟩
  intro hz
  have hd : ((k.natAbs + 1 : ℕ) : ℤ) ∣ k :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd k (k.natAbs + 1)).mp hz
  have hb := Int.natAbs_le_of_dvd_ne_zero hd hk
  change k.natAbs + 1 ≤ k.natAbs at hb
  omega

/-- This proves Mathlib's actual residual-finiteness property. -/
theorem counterexample_group_residuallyFinite :
    Group.ResiduallyFinite CounterexampleGroup.{u} := by
  classical
  apply Group.residuallyFinite_of_forall_exists_finite_monoidHom
  intro a ha
  have hcoord : ∃ i : Fin 3, Heis.coord a i ≠ 0 := by
    by_contra h
    have hz : ∀ i : Fin 3, Heis.coord a i = 0 := by
      intro i
      by_contra hi
      exact h ⟨i, hi⟩
    apply ha
    apply Heis.ext
    · exact hz 0
    · exact hz 1
    · exact hz 2
  obtain ⟨i, hi⟩ := hcoord
  obtain ⟨n, hn, hni⟩ := integer_separation (Heis.coord a i) hi
  letI : NeZero n := ⟨by omega⟩
  refine ⟨Heis.{0} (ZMod n), inferInstance, inferInstance, reduction n, ?_⟩
  intro heq
  apply hni
  have heq' := congrArg (fun b : Heis.{0} (ZMod n) => Heis.coord b i) heq
  fin_cases i <;> simpa [Heis.coord, reduction] using heq'

/-! ## The formula has exactly two values -/

/-- Elementary integer arithmetic, kept independent of group theory. -/
theorem integer_factor_of_one (p q : ℤ) (h : p * q = 1) :
    p = 1 ∨ p = -1 := by
  by_cases hp : p = 1
  · exact Or.inl hp
  right
  by_contra hm
  have hp0 : p ≠ 0 := by
    intro heq
    simp [heq] at h
  by_cases hpos : 0 < p
  · have hp2 : 2 ≤ p := by omega
    have hqpos : 0 < q := by
      by_contra! hq
      have hnonpos := mul_nonpos_of_nonneg_of_nonpos hpos.le hq
      linarith
    have hq1 : 1 ≤ q := by omega
    have hprod := mul_le_mul_of_nonneg_right hp2 hqpos.le
    nlinarith
  · have hp2 : p ≤ -2 := by omega
    have hqneg : q < 0 := by
      by_contra! hq
      have hnonpos := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hpos) hq
      linarith
    have hq1 : q ≤ -1 := by omega
    have hprod := mul_le_mul_of_nonpos_right hp2 hqneg.le
    nlinarith

/-- Any value of the formula is one of the two central unit coordinates. -/
theorem counterexample_values_bound (x : CounterexampleGroup.{u})
    (hx : x ∈ values (G := CounterexampleGroup.{u}) counterexampleFormula) :
    x = Heis.central (1 : ℤ) ∨ x = Heis.central (-1 : ℤ) := by
  obtain ⟨a, b, hab, h⟩ := (mem_values_iff x).mp hx
  obtain ⟨c, d, hac, hbc, hbd, had⟩ :=
    h (Heis.central (1 : ℤ)) (Heis.central_commutes (1 : ℤ))
  have hac' : Heis.det a c = 1 := by
    simpa only [Heis.groupComm_eq, Heis.central_z] using congrArg Heis.z hac
  have hbc' : Heis.det b c = 0 := by
    simpa only [Heis.groupComm_eq, Heis.central_z, Heis.one_z]
      using congrArg Heis.z hbc
  have hbd' : Heis.det b d = 1 := by
    simpa only [Heis.groupComm_eq, Heis.central_z] using congrArg Heis.z hbd
  have had' : Heis.det a d = 0 := by
    simpa only [Heis.groupComm_eq, Heis.central_z, Heis.one_z]
      using congrArg Heis.z had
  have hunit : Heis.det a b * Heis.det c d = 1 := by
    rw [Heis.det_identity, hac', hbc', hbd', had'] <;> norm_num
  rcases integer_factor_of_one (Heis.det a b) (Heis.det c d) hunit with hp | hm
  · left
    calc
      x = groupComm a b := hab.symm
      _ = Heis.central (Heis.det a b) := Heis.groupComm_eq a b
      _ = Heis.central (1 : ℤ) := by rw [hp]
  · right
    calc
      x = groupComm a b := hab.symm
      _ = Heis.central (Heis.det a b) := Heis.groupComm_eq a b
      _ = Heis.central (-1 : ℤ) := by rw [hm]

/-- Testing centrality against two explicitly given elements suffices. -/
theorem central_coordinates (a : CounterexampleGroup.{u})
    (ha : ∀ b : CounterexampleGroup.{u}, a * b = b * a) :
    a.x = 0 ∧ a.y = 0 := by
  have h₁ := congrArg Heis.z (ha (⟨1, 0, 0⟩ : CounterexampleGroup.{u}))
  have h₂ := congrArg Heis.z (ha (⟨0, 1, 0⟩ : CounterexampleGroup.{u}))
  have hy : a.z = a.z + a.y := by
    simpa only [Heis.mul_z, mul_zero, zero_mul, one_mul, mul_one,
      add_zero, zero_add] using h₁
  have hx : a.z + a.x = a.z := by
    simpa only [Heis.mul_z, mul_zero, zero_mul, one_mul, mul_one,
      add_zero, zero_add] using h₂
  constructor <;> linarith

/-- The positive central generator really satisfies the full formula. -/
theorem counterexample_positive_mem :
    (Heis.central (1 : ℤ) : CounterexampleGroup.{u}) ∈
      values (G := CounterexampleGroup.{u}) counterexampleFormula := by
  apply (mem_values_iff _).mpr
  refine ⟨⟨1, 0, 0⟩, ⟨0, 1, 0⟩, ?_, ?_⟩
  · apply Heis.ext <;> simp [Heis.groupComm_eq, Heis.det, Heis.central]
  · intro y hy
    obtain ⟨hx, hy'⟩ := central_coordinates y hy
    refine ⟨⟨0, y.z, 0⟩, ⟨-y.z, 0, 0⟩, ?_, ?_, ?_, ?_⟩
    all_goals
      apply Heis.ext <;>
        simp [Heis.groupComm_eq, Heis.det, Heis.central, hx, hy']

/-- The inverse generator also satisfies the full formula. -/
theorem counterexample_negative_mem :
    (Heis.central (-1 : ℤ) : CounterexampleGroup.{u}) ∈
      values (G := CounterexampleGroup.{u}) counterexampleFormula := by
  apply (mem_values_iff _).mpr
  refine ⟨⟨1, 0, 0⟩, ⟨0, -1, 0⟩, ?_, ?_⟩
  · apply Heis.ext <;> simp [Heis.groupComm_eq, Heis.det, Heis.central]
  · intro y hy
    obtain ⟨hx, hy'⟩ := central_coordinates y hy
    refine ⟨⟨0, y.z, 0⟩, ⟨y.z, 0, 0⟩, ?_, ?_, ?_, ?_⟩
    all_goals
      apply Heis.ext <;>
        simp [Heis.groupComm_eq, Heis.det, Heis.central, hx, hy']

theorem counterexample_values_eq :
    values (G := CounterexampleGroup.{u}) counterexampleFormula =
      {Heis.central (1 : ℤ), Heis.central (-1 : ℤ)} := by
  apply Set.ext
  intro x
  constructor
  · intro hx
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff]
      using counterexample_values_bound x hx
  · intro hx
    rcases (show x = Heis.central (1 : ℤ) ∨ x = Heis.central (-1 : ℤ) from hx)
      with hp | hm
    · rw [hp]
      exact counterexample_positive_mem
    · rw [hm]
      exact counterexample_negative_mem

/-- The first of the two finite/infinite facts used by the caller. -/
theorem counterexample_values_finite :
    (values (G := CounterexampleGroup.{u}) counterexampleFormula).Finite := by
  rw [counterexample_values_eq]
  exact (Set.finite_singleton (Heis.central (-1 : ℤ))).insert
    (Heis.central (1 : ℤ))

/-! ## The subgroup generated by the values is infinite -/

@[simp] theorem central_one_pow (n : ℕ) :
    (Heis.central (1 : ℤ) : CounterexampleGroup.{u}) ^ n =
      Heis.central (n : ℤ) := by
  induction n with
  | zero =>
    rw [pow_zero] <;> rfl
  | succ n ih =>
    simpa only [pow_succ, ih, Heis.central_mul, Nat.cast_succ]

/-- The second finite/infinite fact used by the caller. -/
theorem counterexample_closure_infinite :
    ¬ ((Subgroup.closure
      (values (G := CounterexampleGroup.{u}) counterexampleFormula) :
        Subgroup CounterexampleGroup.{u}) : Set CounterexampleGroup.{u}).Finite := by
  intro hfinite
  have hinj : Function.Injective
      (fun n : ℕ => (Heis.central (1 : ℤ) : CounterexampleGroup.{u}) ^ n) := by
    intro m n h
    have hz := congrArg Heis.z h
    have hmn : (m : ℤ) = (n : ℤ) := by
      simpa only [central_one_pow, Heis.central_z] using hz
    exact Int.ofNat_injective hmn
  have hsub :
      Set.range (fun n : ℕ => (Heis.central (1 : ℤ) : CounterexampleGroup.{u}) ^ n) ⊆
        (Subgroup.closure
          (values (G := CounterexampleGroup.{u}) counterexampleFormula) :
            Set CounterexampleGroup.{u}) := by
    rintro x ⟨n, rfl⟩
    exact (Subgroup.closure
      (values (G := CounterexampleGroup.{u}) counterexampleFormula)).pow_mem
        (Subgroup.subset_closure counterexample_positive_mem) n
  exact (Set.infinite_range_of_injective hinj) (hfinite.subset hsub)

end Kourovka21106
