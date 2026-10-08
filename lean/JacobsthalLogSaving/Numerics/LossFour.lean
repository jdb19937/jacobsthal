import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# Exact evaluation of the fourth omission loss integral

`loss4Kernel s t u x` is the integrand of the 4-fold iterated integral to which `omissionLossTerm 3`
reduces (see `FourthLoss.lean`); here the integral is evaluated in closed form by explicit primitives,
one integration level at a time, in the style of the vendored `LossBounds.lean`.
-/

namespace JacobsthalLogSaving.Numerics

open Set MeasureTheory

noncomputable def loss4Kernel (s t u x : ℝ) : ℝ :=
  2*((((x+u+t)/2+s)^3-((x+2*u)/2)^3)/3-((x+u+t)/2+s-(x+2*u)/2))/(x*u*t*s^2)


noncomputable def prim4s (s t u x : ℝ) : ℝ :=
  (((-1/2:ℝ)) * (s^1)⁻¹)
  + (((1:ℝ) * (t^1)⁻¹) * (Real.log s))
  + (((1:ℝ) * (u^1)⁻¹) * (Real.log s))
  + (((1:ℝ) * (x^1)⁻¹) * (Real.log s))
  + (((1:ℝ) * (u^1)⁻¹ * (t^1)⁻¹) * s)
  + (((1:ℝ) * (x^1)⁻¹ * (t^1)⁻¹) * s)
  + (((1:ℝ) * (x^1)⁻¹ * (u^1)⁻¹) * s)
  + (((1:ℝ) * (x^1)⁻¹ * (u^1)⁻¹) * (s^1)⁻¹)
  + (((-1:ℝ) * (x^1)⁻¹ * (t^1)⁻¹) * (s^1)⁻¹)
  + (((-1/4:ℝ) * (u^1)⁻¹ * t) * (s^1)⁻¹)
  + (((-1/4:ℝ) * (x^1)⁻¹ * t) * (s^1)⁻¹)
  + (((-1/4:ℝ) * (x^1)⁻¹ * u) * (s^1)⁻¹)
  + (((-1/4:ℝ) * x * (u^1)⁻¹) * (s^1)⁻¹)
  + (((1/4:ℝ) * x * (t^1)⁻¹) * (s^1)⁻¹)
  + (((3/4:ℝ) * u * (t^1)⁻¹) * (s^1)⁻¹)
  + (((1/2:ℝ) * (x^1)⁻¹ * (u^1)⁻¹ * t) * (Real.log s))
  + (((1/2:ℝ) * (x^1)⁻¹ * u * (t^1)⁻¹) * (Real.log s))
  + (((1/2:ℝ) * x * (u^1)⁻¹ * (t^1)⁻¹) * (Real.log s))
  + (((-2:ℝ) * (x^1)⁻¹ * (u^1)⁻¹ * (t^1)⁻¹) * (Real.log s))
  + (((-1/12:ℝ) * (x^1)⁻¹ * (u^1)⁻¹ * t^2) * (s^1)⁻¹)
  + (((1/3:ℝ) * (x^1)⁻¹ * (u^1)⁻¹ * (t^1)⁻¹) * s^2)
  + (((7/12:ℝ) * (x^1)⁻¹ * u^2 * (t^1)⁻¹) * (s^1)⁻¹)

noncomputable def middle4 (t u x : ℝ) : ℝ :=
  (((1/2:ℝ)))
  + (((-1/2:ℝ)) * (t^1)⁻¹)
  + (((3/4:ℝ) * (u^1)⁻¹))
  + (((3/4:ℝ) * (x^1)⁻¹))
  + (((1:ℝ)) * (t^1)⁻¹ * (Real.log t))
  + (((1:ℝ) * (u^1)⁻¹) * (Real.log t))
  + (((1:ℝ) * (x^1)⁻¹) * (Real.log t))
  + (((-1:ℝ) * (u^1)⁻¹) * (t^1)⁻¹)
  + (((-1:ℝ) * (x^1)⁻¹) * (t^2)⁻¹)
  + (((-2:ℝ) * (x^1)⁻¹ * (u^1)⁻¹))
  + (((-3/4:ℝ) * u) * (t^1)⁻¹)
  + (((-1/4:ℝ) * x) * (t^1)⁻¹)
  + (((1/4:ℝ) * (u^1)⁻¹) * t)
  + (((1/4:ℝ) * (x^1)⁻¹) * t)
  + (((1/4:ℝ) * (x^1)⁻¹ * u))
  + (((1/4:ℝ) * x) * (t^2)⁻¹)
  + (((1/4:ℝ) * x * (u^1)⁻¹))
  + (((3/4:ℝ) * u) * (t^2)⁻¹)
  + (((-7/12:ℝ) * (x^1)⁻¹ * u^2) * (t^1)⁻¹)
  + (((-1/4:ℝ) * (x^1)⁻¹ * u) * (t^1)⁻¹)
  + (((-1/4:ℝ) * x * (u^1)⁻¹) * (t^1)⁻¹)
  + (((1/12:ℝ) * (x^1)⁻¹ * (u^1)⁻¹) * t^2)
  + (((2/3:ℝ) * (x^1)⁻¹ * (u^1)⁻¹) * (t^1)⁻¹)
  + (((5/4:ℝ) * (x^1)⁻¹ * (u^1)⁻¹) * t)
  + (((7/12:ℝ) * (x^1)⁻¹ * u^2) * (t^2)⁻¹)
  + (((1/2:ℝ) * (x^1)⁻¹ * (u^1)⁻¹) * t * (Real.log t))
  + (((1/2:ℝ) * (x^1)⁻¹ * u) * (t^1)⁻¹ * (Real.log t))
  + (((1/2:ℝ) * x * (u^1)⁻¹) * (t^1)⁻¹ * (Real.log t))
  + (((-2:ℝ) * (x^1)⁻¹ * (u^1)⁻¹) * (t^1)⁻¹ * (Real.log t))

noncomputable def prim4t (t u x : ℝ) : ℝ :=
  (((1/2:ℝ)) * t)
  + (((1/2:ℝ)) * (Real.log t)^2)
  + (((-1/2:ℝ)) * (Real.log t))
  + (((1:ℝ) * (x^1)⁻¹) * (t^1)⁻¹)
  + (((-1:ℝ) * (u^1)⁻¹) * (Real.log t))
  + (((-3/4:ℝ) * u) * (Real.log t))
  + (((-3/4:ℝ) * u) * (t^1)⁻¹)
  + (((-1/4:ℝ) * x) * (Real.log t))
  + (((-1/4:ℝ) * (u^1)⁻¹) * t)
  + (((-1/4:ℝ) * (x^1)⁻¹) * t)
  + (((-1/4:ℝ) * x) * (t^1)⁻¹)
  + (((1/8:ℝ) * (u^1)⁻¹) * t^2)
  + (((1/8:ℝ) * (x^1)⁻¹) * t^2)
  + (((1:ℝ) * (u^1)⁻¹) * t * (Real.log t))
  + (((1:ℝ) * (x^1)⁻¹) * t * (Real.log t))
  + (((1/2:ℝ) * (x^1)⁻¹ * (u^1)⁻¹) * t^2)
  + (((-1:ℝ) * (x^1)⁻¹ * (u^1)⁻¹) * (Real.log t)^2)
  + (((-2:ℝ) * (x^1)⁻¹ * (u^1)⁻¹) * t)
  + (((-7/12:ℝ) * (x^1)⁻¹ * u^2) * (Real.log t))
  + (((-7/12:ℝ) * (x^1)⁻¹ * u^2) * (t^1)⁻¹)
  + (((-1/4:ℝ) * (x^1)⁻¹ * u) * (Real.log t))
  + (((-1/4:ℝ) * x * (u^1)⁻¹) * (Real.log t))
  + (((1/4:ℝ) * (x^1)⁻¹ * u) * t)
  + (((1/4:ℝ) * x * (u^1)⁻¹) * t)
  + (((1/4:ℝ) * (x^1)⁻¹ * u) * (Real.log t)^2)
  + (((1/4:ℝ) * x * (u^1)⁻¹) * (Real.log t)^2)
  + (((1/36:ℝ) * (x^1)⁻¹ * (u^1)⁻¹) * t^3)
  + (((2/3:ℝ) * (x^1)⁻¹ * (u^1)⁻¹) * (Real.log t))
  + (((1/4:ℝ) * (x^1)⁻¹ * (u^1)⁻¹) * t^2 * (Real.log t))

noncomputable def reduced4 (u x : ℝ) : ℝ :=
  (((-3/2:ℝ)))
  + (((1/2:ℝ)) * (Real.log u))
  + (((1/2:ℝ) * x))
  + (((1/2:ℝ)) * (Real.log u)^2)
  + (((-23/8:ℝ) * (x^1)⁻¹))
  + (((1/8:ℝ)) * (u^1)⁻¹)
  + (((11/8:ℝ)) * u)
  + (((-1:ℝ)) * (u^1)⁻¹ * (Real.log u))
  + (((-7/12:ℝ) * (x^1)⁻¹) * u)
  + (((-3/4:ℝ)) * u * (Real.log u))
  + (((-1/2:ℝ) * x) * (u^1)⁻¹)
  + (((-1/4:ℝ) * x) * (Real.log u))
  + (((71/72:ℝ) * (x^1)⁻¹) * u^2)
  + (((89/36:ℝ) * (x^1)⁻¹) * (u^1)⁻¹)
  + (((1:ℝ) * (x^1)⁻¹) * u * (Real.log u))
  + (((-1:ℝ) * (x^1)⁻¹) * (u^1)⁻¹ * (Real.log u)^2)
  + (((-7/12:ℝ) * (x^1)⁻¹) * u^2 * (Real.log u))
  + (((-1/4:ℝ) * x) * (u^1)⁻¹ * (Real.log u))
  + (((1/4:ℝ) * (x^1)⁻¹) * u * (Real.log u)^2)
  + (((1/4:ℝ) * x) * (u^1)⁻¹ * (Real.log u)^2)
  + (((2/3:ℝ) * (x^1)⁻¹) * (u^1)⁻¹ * (Real.log u))

noncomputable def prim4u (u x : ℝ) : ℝ :=
  (((-1:ℝ)) * u)
  + (((-1/2:ℝ)) * (Real.log u)^2)
  + (((1/8:ℝ)) * (Real.log u))
  + (((7/8:ℝ)) * u^2)
  + (((1/2:ℝ)) * u * (Real.log u)^2)
  + (((-23/8:ℝ) * (x^1)⁻¹) * u)
  + (((-23/48:ℝ) * (x^1)⁻¹) * u^2)
  + (((-3/8:ℝ)) * u^2 * (Real.log u))
  + (((-1/2:ℝ)) * u * (Real.log u))
  + (((-1/2:ℝ) * x) * (Real.log u))
  + (((-1/3:ℝ) * (x^1)⁻¹) * (Real.log u)^3)
  + (((-1/8:ℝ) * x) * (Real.log u)^2)
  + (((1/3:ℝ) * (x^1)⁻¹) * (Real.log u)^2)
  + (((1/12:ℝ) * x) * (Real.log u)^3)
  + (((3/4:ℝ) * x) * u)
  + (((85/216:ℝ) * (x^1)⁻¹) * u^3)
  + (((89/36:ℝ) * (x^1)⁻¹) * (Real.log u))
  + (((-7/36:ℝ) * (x^1)⁻¹) * u^3 * (Real.log u))
  + (((-1/4:ℝ) * x) * u * (Real.log u))
  + (((1/8:ℝ) * (x^1)⁻¹) * u^2 * (Real.log u)^2)
  + (((3/8:ℝ) * (x^1)⁻¹) * u^2 * (Real.log u))

noncomputable def outer4 (x : ℝ) : ℝ :=
  (((-11/4:ℝ)))
  + (((-107/48:ℝ)) * x)
  + (((-1/2:ℝ)) * (Real.log x)^2)
  + (((1/8:ℝ)) * (Real.log x))
  + (((109/54:ℝ)) * x^2)
  + (((1279/432:ℝ)) * (x^1)⁻¹)
  + (((1/2:ℝ)) * x * (Real.log x)^2)
  + (((-59/72:ℝ)) * x^2 * (Real.log x))
  + (((-5/8:ℝ)) * x * (Real.log x))
  + (((-1/3:ℝ)) * (x^1)⁻¹ * (Real.log x)^3)
  + (((1/3:ℝ)) * (x^1)⁻¹ * (Real.log x)^2)
  + (((1/12:ℝ)) * x * (Real.log x)^3)
  + (((89/36:ℝ)) * (x^1)⁻¹ * (Real.log x))

noncomputable def prim4x (x : ℝ) : ℝ :=
  (((-83/96:ℝ)) * x^2)
  + (((-31/8:ℝ)) * x)
  + (((-1/12:ℝ)) * (Real.log x)^4)
  + (((1/9:ℝ)) * (Real.log x)^3)
  + (((55/72:ℝ)) * x^3)
  + (((89/72:ℝ)) * (Real.log x)^2)
  + (((1279/432:ℝ)) * (Real.log x))
  + (((-59/216:ℝ)) * x^3 * (Real.log x))
  + (((-1/2:ℝ)) * x^2 * (Real.log x))
  + (((-1/2:ℝ)) * x * (Real.log x)^2)
  + (((1/24:ℝ)) * x^2 * (Real.log x)^3)
  + (((3/16:ℝ)) * x^2 * (Real.log x)^2)
  + (((9/8:ℝ)) * x * (Real.log x))

theorem prim4s_deriv (s t u x : ℝ) (hs : 0 < s) (ht : 0 < t) (hu : 0 < u) (hx : 0 < x) :
    HasDerivAt (fun s : ℝ => prim4s s t u x) (loss4Kernel s t u x) s := by
  unfold prim4s loss4Kernel
  have h0 := ((hasDerivAt_const s ((-1/2:ℝ))).mul (((hasDerivAt_id s).pow 1).inv (by change s^1 ≠ 0; positivity)))
  have h1 := ((hasDerivAt_const s ((1:ℝ) * (t^1)⁻¹)).mul ((hasDerivAt_id s).log (by positivity)))
  have h2 := ((hasDerivAt_const s ((1:ℝ) * (u^1)⁻¹)).mul ((hasDerivAt_id s).log (by positivity)))
  have h3 := ((hasDerivAt_const s ((1:ℝ) * (x^1)⁻¹)).mul ((hasDerivAt_id s).log (by positivity)))
  have h4 := ((hasDerivAt_const s ((1:ℝ) * (u^1)⁻¹ * (t^1)⁻¹)).mul (hasDerivAt_id s))
  have h5 := ((hasDerivAt_const s ((1:ℝ) * (x^1)⁻¹ * (t^1)⁻¹)).mul (hasDerivAt_id s))
  have h6 := ((hasDerivAt_const s ((1:ℝ) * (x^1)⁻¹ * (u^1)⁻¹)).mul (hasDerivAt_id s))
  have h7 := ((hasDerivAt_const s ((1:ℝ) * (x^1)⁻¹ * (u^1)⁻¹)).mul (((hasDerivAt_id s).pow 1).inv (by change s^1 ≠ 0; positivity)))
  have h8 := ((hasDerivAt_const s ((-1:ℝ) * (x^1)⁻¹ * (t^1)⁻¹)).mul (((hasDerivAt_id s).pow 1).inv (by change s^1 ≠ 0; positivity)))
  have h9 := ((hasDerivAt_const s ((-1/4:ℝ) * (u^1)⁻¹ * t)).mul (((hasDerivAt_id s).pow 1).inv (by change s^1 ≠ 0; positivity)))
  have h10 := ((hasDerivAt_const s ((-1/4:ℝ) * (x^1)⁻¹ * t)).mul (((hasDerivAt_id s).pow 1).inv (by change s^1 ≠ 0; positivity)))
  have h11 := ((hasDerivAt_const s ((-1/4:ℝ) * (x^1)⁻¹ * u)).mul (((hasDerivAt_id s).pow 1).inv (by change s^1 ≠ 0; positivity)))
  have h12 := ((hasDerivAt_const s ((-1/4:ℝ) * x * (u^1)⁻¹)).mul (((hasDerivAt_id s).pow 1).inv (by change s^1 ≠ 0; positivity)))
  have h13 := ((hasDerivAt_const s ((1/4:ℝ) * x * (t^1)⁻¹)).mul (((hasDerivAt_id s).pow 1).inv (by change s^1 ≠ 0; positivity)))
  have h14 := ((hasDerivAt_const s ((3/4:ℝ) * u * (t^1)⁻¹)).mul (((hasDerivAt_id s).pow 1).inv (by change s^1 ≠ 0; positivity)))
  have h15 := ((hasDerivAt_const s ((1/2:ℝ) * (x^1)⁻¹ * (u^1)⁻¹ * t)).mul ((hasDerivAt_id s).log (by positivity)))
  have h16 := ((hasDerivAt_const s ((1/2:ℝ) * (x^1)⁻¹ * u * (t^1)⁻¹)).mul ((hasDerivAt_id s).log (by positivity)))
  have h17 := ((hasDerivAt_const s ((1/2:ℝ) * x * (u^1)⁻¹ * (t^1)⁻¹)).mul ((hasDerivAt_id s).log (by positivity)))
  have h18 := ((hasDerivAt_const s ((-2:ℝ) * (x^1)⁻¹ * (u^1)⁻¹ * (t^1)⁻¹)).mul ((hasDerivAt_id s).log (by positivity)))
  have h19 := ((hasDerivAt_const s ((-1/12:ℝ) * (x^1)⁻¹ * (u^1)⁻¹ * t^2)).mul (((hasDerivAt_id s).pow 1).inv (by change s^1 ≠ 0; positivity)))
  have h20 := ((hasDerivAt_const s ((1/3:ℝ) * (x^1)⁻¹ * (u^1)⁻¹ * (t^1)⁻¹)).mul ((hasDerivAt_id s).pow 2))
  have h21 := ((hasDerivAt_const s ((7/12:ℝ) * (x^1)⁻¹ * u^2 * (t^1)⁻¹)).mul (((hasDerivAt_id s).pow 1).inv (by change s^1 ≠ 0; positivity)))
  have hd := (((((((((((((((((((((h0.add h1).add h2).add h3).add h4).add h5).add h6).add h7).add h8).add h9).add h10).add h11).add h12).add h13).add h14).add h15).add h16).add h17).add h18).add h19).add h20).add h21)
  refine hd.congr_deriv ?_
  simp only [id_eq,Pi.pow_apply,Pi.inv_apply]
  field_simp
  ring

theorem prim4t_deriv (t u x : ℝ) (ht : 0 < t) (hu : 0 < u) (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => prim4t t u x) (middle4 t u x) t := by
  unfold prim4t middle4
  have h0 := ((hasDerivAt_const t ((1/2:ℝ))).mul (hasDerivAt_id t))
  have h1 := ((hasDerivAt_const t ((1/2:ℝ))).mul (((hasDerivAt_id t).log (by positivity)).pow 2))
  have h2 := ((hasDerivAt_const t ((-1/2:ℝ))).mul ((hasDerivAt_id t).log (by positivity)))
  have h3 := ((hasDerivAt_const t ((1:ℝ) * (x^1)⁻¹)).mul (((hasDerivAt_id t).pow 1).inv (by change t^1 ≠ 0; positivity)))
  have h4 := ((hasDerivAt_const t ((-1:ℝ) * (u^1)⁻¹)).mul ((hasDerivAt_id t).log (by positivity)))
  have h5 := ((hasDerivAt_const t ((-3/4:ℝ) * u)).mul ((hasDerivAt_id t).log (by positivity)))
  have h6 := ((hasDerivAt_const t ((-3/4:ℝ) * u)).mul (((hasDerivAt_id t).pow 1).inv (by change t^1 ≠ 0; positivity)))
  have h7 := ((hasDerivAt_const t ((-1/4:ℝ) * x)).mul ((hasDerivAt_id t).log (by positivity)))
  have h8 := ((hasDerivAt_const t ((-1/4:ℝ) * (u^1)⁻¹)).mul (hasDerivAt_id t))
  have h9 := ((hasDerivAt_const t ((-1/4:ℝ) * (x^1)⁻¹)).mul (hasDerivAt_id t))
  have h10 := ((hasDerivAt_const t ((-1/4:ℝ) * x)).mul (((hasDerivAt_id t).pow 1).inv (by change t^1 ≠ 0; positivity)))
  have h11 := ((hasDerivAt_const t ((1/8:ℝ) * (u^1)⁻¹)).mul ((hasDerivAt_id t).pow 2))
  have h12 := ((hasDerivAt_const t ((1/8:ℝ) * (x^1)⁻¹)).mul ((hasDerivAt_id t).pow 2))
  have h13 := (((hasDerivAt_const t ((1:ℝ) * (u^1)⁻¹)).mul (hasDerivAt_id t)).mul ((hasDerivAt_id t).log (by positivity)))
  have h14 := (((hasDerivAt_const t ((1:ℝ) * (x^1)⁻¹)).mul (hasDerivAt_id t)).mul ((hasDerivAt_id t).log (by positivity)))
  have h15 := ((hasDerivAt_const t ((1/2:ℝ) * (x^1)⁻¹ * (u^1)⁻¹)).mul ((hasDerivAt_id t).pow 2))
  have h16 := ((hasDerivAt_const t ((-1:ℝ) * (x^1)⁻¹ * (u^1)⁻¹)).mul (((hasDerivAt_id t).log (by positivity)).pow 2))
  have h17 := ((hasDerivAt_const t ((-2:ℝ) * (x^1)⁻¹ * (u^1)⁻¹)).mul (hasDerivAt_id t))
  have h18 := ((hasDerivAt_const t ((-7/12:ℝ) * (x^1)⁻¹ * u^2)).mul ((hasDerivAt_id t).log (by positivity)))
  have h19 := ((hasDerivAt_const t ((-7/12:ℝ) * (x^1)⁻¹ * u^2)).mul (((hasDerivAt_id t).pow 1).inv (by change t^1 ≠ 0; positivity)))
  have h20 := ((hasDerivAt_const t ((-1/4:ℝ) * (x^1)⁻¹ * u)).mul ((hasDerivAt_id t).log (by positivity)))
  have h21 := ((hasDerivAt_const t ((-1/4:ℝ) * x * (u^1)⁻¹)).mul ((hasDerivAt_id t).log (by positivity)))
  have h22 := ((hasDerivAt_const t ((1/4:ℝ) * (x^1)⁻¹ * u)).mul (hasDerivAt_id t))
  have h23 := ((hasDerivAt_const t ((1/4:ℝ) * x * (u^1)⁻¹)).mul (hasDerivAt_id t))
  have h24 := ((hasDerivAt_const t ((1/4:ℝ) * (x^1)⁻¹ * u)).mul (((hasDerivAt_id t).log (by positivity)).pow 2))
  have h25 := ((hasDerivAt_const t ((1/4:ℝ) * x * (u^1)⁻¹)).mul (((hasDerivAt_id t).log (by positivity)).pow 2))
  have h26 := ((hasDerivAt_const t ((1/36:ℝ) * (x^1)⁻¹ * (u^1)⁻¹)).mul ((hasDerivAt_id t).pow 3))
  have h27 := ((hasDerivAt_const t ((2/3:ℝ) * (x^1)⁻¹ * (u^1)⁻¹)).mul ((hasDerivAt_id t).log (by positivity)))
  have h28 := (((hasDerivAt_const t ((1/4:ℝ) * (x^1)⁻¹ * (u^1)⁻¹)).mul ((hasDerivAt_id t).pow 2)).mul ((hasDerivAt_id t).log (by positivity)))
  have hd := ((((((((((((((((((((((((((((h0.add h1).add h2).add h3).add h4).add h5).add h6).add h7).add h8).add h9).add h10).add h11).add h12).add h13).add h14).add h15).add h16).add h17).add h18).add h19).add h20).add h21).add h22).add h23).add h24).add h25).add h26).add h27).add h28)
  refine hd.congr_deriv ?_
  simp only [id_eq,Pi.pow_apply,Pi.inv_apply,Pi.mul_apply]
  field_simp
  ring

theorem prim4u_deriv (u x : ℝ) (hu : 0 < u) (hx : 0 < x) :
    HasDerivAt (fun u : ℝ => prim4u u x) (reduced4 u x) u := by
  unfold prim4u reduced4
  have h0 := ((hasDerivAt_const u ((-1:ℝ))).mul (hasDerivAt_id u))
  have h1 := ((hasDerivAt_const u ((-1/2:ℝ))).mul (((hasDerivAt_id u).log (by positivity)).pow 2))
  have h2 := ((hasDerivAt_const u ((1/8:ℝ))).mul ((hasDerivAt_id u).log (by positivity)))
  have h3 := ((hasDerivAt_const u ((7/8:ℝ))).mul ((hasDerivAt_id u).pow 2))
  have h4 := (((hasDerivAt_const u ((1/2:ℝ))).mul (hasDerivAt_id u)).mul (((hasDerivAt_id u).log (by positivity)).pow 2))
  have h5 := ((hasDerivAt_const u ((-23/8:ℝ) * (x^1)⁻¹)).mul (hasDerivAt_id u))
  have h6 := ((hasDerivAt_const u ((-23/48:ℝ) * (x^1)⁻¹)).mul ((hasDerivAt_id u).pow 2))
  have h7 := (((hasDerivAt_const u ((-3/8:ℝ))).mul ((hasDerivAt_id u).pow 2)).mul ((hasDerivAt_id u).log (by positivity)))
  have h8 := (((hasDerivAt_const u ((-1/2:ℝ))).mul (hasDerivAt_id u)).mul ((hasDerivAt_id u).log (by positivity)))
  have h9 := ((hasDerivAt_const u ((-1/2:ℝ) * x)).mul ((hasDerivAt_id u).log (by positivity)))
  have h10 := ((hasDerivAt_const u ((-1/3:ℝ) * (x^1)⁻¹)).mul (((hasDerivAt_id u).log (by positivity)).pow 3))
  have h11 := ((hasDerivAt_const u ((-1/8:ℝ) * x)).mul (((hasDerivAt_id u).log (by positivity)).pow 2))
  have h12 := ((hasDerivAt_const u ((1/3:ℝ) * (x^1)⁻¹)).mul (((hasDerivAt_id u).log (by positivity)).pow 2))
  have h13 := ((hasDerivAt_const u ((1/12:ℝ) * x)).mul (((hasDerivAt_id u).log (by positivity)).pow 3))
  have h14 := ((hasDerivAt_const u ((3/4:ℝ) * x)).mul (hasDerivAt_id u))
  have h15 := ((hasDerivAt_const u ((85/216:ℝ) * (x^1)⁻¹)).mul ((hasDerivAt_id u).pow 3))
  have h16 := ((hasDerivAt_const u ((89/36:ℝ) * (x^1)⁻¹)).mul ((hasDerivAt_id u).log (by positivity)))
  have h17 := (((hasDerivAt_const u ((-7/36:ℝ) * (x^1)⁻¹)).mul ((hasDerivAt_id u).pow 3)).mul ((hasDerivAt_id u).log (by positivity)))
  have h18 := (((hasDerivAt_const u ((-1/4:ℝ) * x)).mul (hasDerivAt_id u)).mul ((hasDerivAt_id u).log (by positivity)))
  have h19 := (((hasDerivAt_const u ((1/8:ℝ) * (x^1)⁻¹)).mul ((hasDerivAt_id u).pow 2)).mul (((hasDerivAt_id u).log (by positivity)).pow 2))
  have h20 := (((hasDerivAt_const u ((3/8:ℝ) * (x^1)⁻¹)).mul ((hasDerivAt_id u).pow 2)).mul ((hasDerivAt_id u).log (by positivity)))
  have hd := ((((((((((((((((((((h0.add h1).add h2).add h3).add h4).add h5).add h6).add h7).add h8).add h9).add h10).add h11).add h12).add h13).add h14).add h15).add h16).add h17).add h18).add h19).add h20)
  refine hd.congr_deriv ?_
  simp only [id_eq,Pi.pow_apply,Pi.mul_apply]
  field_simp
  ring

theorem prim4x_deriv (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => prim4x x) (outer4 x) x := by
  unfold prim4x outer4
  have h0 := ((hasDerivAt_const x ((-83/96:ℝ))).mul ((hasDerivAt_id x).pow 2))
  have h1 := ((hasDerivAt_const x ((-31/8:ℝ))).mul (hasDerivAt_id x))
  have h2 := ((hasDerivAt_const x ((-1/12:ℝ))).mul (((hasDerivAt_id x).log (by positivity)).pow 4))
  have h3 := ((hasDerivAt_const x ((1/9:ℝ))).mul (((hasDerivAt_id x).log (by positivity)).pow 3))
  have h4 := ((hasDerivAt_const x ((55/72:ℝ))).mul ((hasDerivAt_id x).pow 3))
  have h5 := ((hasDerivAt_const x ((89/72:ℝ))).mul (((hasDerivAt_id x).log (by positivity)).pow 2))
  have h6 := ((hasDerivAt_const x ((1279/432:ℝ))).mul ((hasDerivAt_id x).log (by positivity)))
  have h7 := (((hasDerivAt_const x ((-59/216:ℝ))).mul ((hasDerivAt_id x).pow 3)).mul ((hasDerivAt_id x).log (by positivity)))
  have h8 := (((hasDerivAt_const x ((-1/2:ℝ))).mul ((hasDerivAt_id x).pow 2)).mul ((hasDerivAt_id x).log (by positivity)))
  have h9 := (((hasDerivAt_const x ((-1/2:ℝ))).mul (hasDerivAt_id x)).mul (((hasDerivAt_id x).log (by positivity)).pow 2))
  have h10 := (((hasDerivAt_const x ((1/24:ℝ))).mul ((hasDerivAt_id x).pow 2)).mul (((hasDerivAt_id x).log (by positivity)).pow 3))
  have h11 := (((hasDerivAt_const x ((3/16:ℝ))).mul ((hasDerivAt_id x).pow 2)).mul (((hasDerivAt_id x).log (by positivity)).pow 2))
  have h12 := (((hasDerivAt_const x ((9/8:ℝ))).mul (hasDerivAt_id x)).mul ((hasDerivAt_id x).log (by positivity)))
  have hd := ((((((((((((h0.add h1).add h2).add h3).add h4).add h5).add h6).add h7).add h8).add h9).add h10).add h11).add h12)
  refine hd.congr_deriv ?_
  simp only [id_eq,Pi.pow_apply,Pi.mul_apply]
  field_simp
  ring

noncomputable def L4value : ℝ :=
  ((-323/288:ℝ))
  + ((-1/12:ℝ) * (Real.log (2:ℝ))^4)
  + ((5/18:ℝ) * (Real.log (2:ℝ))^3)
  + ((71/72:ℝ) * (Real.log (2:ℝ))^2)
  + ((443/432:ℝ) * (Real.log (2:ℝ)))

theorem loss4Kernel_integrable {t u x : ℝ} (ht : 1 ≤ t) (hu : 0 < u) (hx : 0 < x) :
    IntervalIntegrable (fun s : ℝ => loss4Kernel s t u x) volume 1 t := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le ht]
  intro s hs
  have hs0 : s ≠ 0 := by have := hs.1; linarith
  have ht0 : t ≠ 0 := by linarith
  have hu0 : u ≠ 0 := hu.ne'
  have hx0 : x ≠ 0 := hx.ne'
  apply ContinuousAt.continuousWithinAt
  unfold loss4Kernel
  fun_prop (disch := simp_all)

theorem middle4_integrable {u x : ℝ} (hu : 1 ≤ u) (hx : 0 < x) :
    IntervalIntegrable (fun t : ℝ => middle4 t u x) volume 1 u := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hu]
  intro t ht
  have ht0 : t ≠ 0 := by have := ht.1; linarith
  have hu0 : u ≠ 0 := by linarith
  have hx0 : x ≠ 0 := hx.ne'
  apply ContinuousAt.continuousWithinAt
  unfold middle4
  fun_prop (disch := simp_all)

theorem reduced4_integrable {x : ℝ} (hx : 1 ≤ x) :
    IntervalIntegrable (fun u : ℝ => reduced4 u x) volume 1 x := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hx]
  intro u hu
  have hu0 : u ≠ 0 := by have := hu.1; linarith
  have hx0 : x ≠ 0 := by linarith
  apply ContinuousAt.continuousWithinAt
  unfold reduced4
  fun_prop (disch := simp_all)

theorem outer4_integrable  :
    IntervalIntegrable (fun x : ℝ => outer4 x) volume 1 2 := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le (by norm_num : (1:ℝ) ≤ 2)]
  intro x hx
  have hx0 : x ≠ 0 := by have := hx.1; linarith
  apply ContinuousAt.continuousWithinAt
  unfold outer4
  fun_prop (disch := simp_all)

theorem loss4_inner_reduction {t u x : ℝ} (ht : 1 ≤ t) (hu : 0 < u) (hx : 0 < x) :
    (∫ s in (1:ℝ)..t, loss4Kernel s t u x) = middle4 t u x := by
  have htpos : 0 < t := by linarith
  have hd : ∀ s ∈ uIcc (1:ℝ) t, HasDerivAt (fun s : ℝ => prim4s s t u x) (loss4Kernel s t u x) s := by
    intro s hs
    rw [uIcc_of_le ht] at hs
    exact prim4s_deriv s t u x (by linarith [hs.1]) htpos hu hx
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (loss4Kernel_integrable ht hu hx)]
  have ht0 : t ≠ 0 := htpos.ne'
  have hu0 : u ≠ 0 := hu.ne'
  have hx0 : x ≠ 0 := hx.ne'
  unfold prim4s middle4
  norm_num
  field_simp
  ring

theorem loss4_middle_reduction {u x : ℝ} (hu : 1 ≤ u) (hx : 0 < x) :
    (∫ t in (1:ℝ)..u, middle4 t u x) = reduced4 u x := by
  have hupos : 0 < u := by linarith
  have hd : ∀ t ∈ uIcc (1:ℝ) u, HasDerivAt (fun t : ℝ => prim4t t u x) (middle4 t u x) t := by
    intro t ht
    rw [uIcc_of_le hu] at ht
    exact prim4t_deriv t u x (by linarith [ht.1]) hupos hx
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (middle4_integrable hu hx)]
  have hu0 : u ≠ 0 := hupos.ne'
  have hx0 : x ≠ 0 := hx.ne'
  unfold prim4t reduced4
  norm_num
  field_simp
  ring

theorem loss4_outer_reduction {x : ℝ} (hx : 1 ≤ x) :
    (∫ u in (1:ℝ)..x, reduced4 u x) = outer4 x := by
  have hxpos : 0 < x := by linarith
  have hd : ∀ u ∈ uIcc (1:ℝ) x, HasDerivAt (fun u : ℝ => prim4u u x) (reduced4 u x) u := by
    intro u hu
    rw [uIcc_of_le hx] at hu
    exact prim4u_deriv u x (by linarith [hu.1]) hxpos
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (reduced4_integrable hx)]
  have hx0 : x ≠ 0 := hxpos.ne'
  unfold prim4u outer4
  norm_num
  field_simp
  ring

theorem loss4_value : (∫ x in (1:ℝ)..2, outer4 x) = L4value := by
  have hd : ∀ x ∈ uIcc (1:ℝ) 2, HasDerivAt (fun x : ℝ => prim4x x) (outer4 x) x := by
    intro x hx
    rw [uIcc_of_le (by norm_num : (1:ℝ) ≤ 2)] at hx
    exact prim4x_deriv x (by linarith [hx.1])
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd outer4_integrable]
  unfold prim4x L4value
  norm_num
  ring

theorem loss4_iterated_eq :
    (∫ x : ℝ in (1:ℝ)..2, ∫ u : ℝ in (1:ℝ)..x, ∫ t : ℝ in (1:ℝ)..u, ∫ s : ℝ in (1:ℝ)..t,
      loss4Kernel s t u x) = L4value := by
  rw [← loss4_value]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le (by norm_num : (1:ℝ) ≤ 2)] at hx
  dsimp only
  rw [← loss4_outer_reduction hx.1]
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le hx.1] at hu
  dsimp only
  rw [← loss4_middle_reduction hu.1 (by linarith [hx.1])]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hu.1] at ht
  dsimp only
  exact loss4_inner_reduction ht.1 (by linarith [hu.1]) (by linarith [hx.1])

theorem L4value_lt : L4value < 1364/10000 := by
  have h1 := Real.log_two_gt_d9
  have h2 := Real.log_two_lt_d9
  have hpos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have e2 : Real.log 2 ^ 2 < 0.6931471808 ^ 2 := pow_lt_pow_left₀ h2 hpos.le (by norm_num)
  have e3 : Real.log 2 ^ 3 < 0.6931471808 ^ 3 := pow_lt_pow_left₀ h2 hpos.le (by norm_num)
  have e4 : 0.6931471803 ^ 4 < Real.log 2 ^ 4 := pow_lt_pow_left₀ h1 (by norm_num) (by norm_num)
  unfold L4value
  norm_num at e2 e3 e4 ⊢
  linarith

theorem L4value_pos : 0 < L4value := by
  have h1 := Real.log_two_gt_d9
  have h2 := Real.log_two_lt_d9
  have hpos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have e2 : 0.6931471803 ^ 2 < Real.log 2 ^ 2 := pow_lt_pow_left₀ h1 (by norm_num) (by norm_num)
  have e3 : 0.6931471803 ^ 3 < Real.log 2 ^ 3 := pow_lt_pow_left₀ h1 (by norm_num) (by norm_num)
  have e4 : Real.log 2 ^ 4 < 0.6931471808 ^ 4 := pow_lt_pow_left₀ h2 hpos.le (by norm_num)
  unfold L4value
  norm_num at e2 e3 e4 ⊢
  linarith

end JacobsthalLogSaving.Numerics
