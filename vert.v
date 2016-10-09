Require Import Classical.
Require Import Reals.
Require Import Fourier.
Require Import seot_util.
Require Import FunctionalExtensionality.
Require Import analysis.
Local Open Scope R_scope.


(* describes coefficents used in a second order polynomial *)
Record coeff : Type := mkcoeff { a : R;  b:R ; c:R }.

(* This construction describes conditions for polynomial with coefficients trj1 to be above and safely vertically separated from a polynomial path with coefficients trj2 by a distance of hp during the time period tb<=t<=te *)
Inductive Γ (trj1 trj2 : coeff) (hp tb te :R) : Prop := 
| quadratic : forall S1 S2 A B C D ,
            A = (a trj1) - (a trj2) ->
            B = (b trj1) - (b trj2) ->
            C = (c trj1) - (c trj2) - hp ->
            D = B^2 - 4*A*C ->
            S1 =(-B - sqrt D)/(2*A) ->
            S2 =(-B + sqrt D)/(2*A) ->
            (tb <= te ->
            A > 0 /\ ((0 <= D /\ (S1 > te \/ S2 < tb)) \/
                       D < 0) \/
            A < 0 /\ (0 < D /\ S2 < tb /\ S1 > te)) ->
              Γ trj1 trj2 hp tb te
| linear : forall A B C,
            A = (a trj1) - (a trj2) ->
            B = (b trj1) - (b trj2) ->
            C = (c trj1) - (c trj2) - hp ->
            (tb <= te ->
              A = 0 /\ (B > 0 /\ -C/B < tb \/
                        B < 0 /\ -C/B >te \/
                        B = 0 /\ C > 0)) ->
            Γ trj1 trj2 hp tb te.


(* Given coefficients a, b, and c, this function defines a trajectory
that describes the altitude of the aircraft for all t
J(t) = a*t^2 + b*t + c
*)
Definition J (z : coeff) (t : R) := (a z) *t^2 + (b z)*t + (c z).

(* 
   This is the proof that shows that Γ does what
   we say it claims to do. Use this as a building block for the 
   rest of the vertical proof 
*)

Theorem safely_separated_second_order_polynomial_interval:
  forall coeffU coeffL hp t1 t2 t,
               t1 <= t <= t2 ->
               (Γ coeffU coeffL hp t1 t2) ->
               hp < J coeffU t-J coeffL t.
Proof.
  intros.
  rename H0 into sfty.
  destruct coeffU as [au bu cu].
  destruct coeffL as [al bl cl].
  unfold J, a, b, c.
  apply (Rplus_lt_reg_r (-hp)).
  setl 0.
  setr ((au-al) * t ^ 2 + (bu-bl)* t + (cu-cl-hp)).

  assert (t1 <= t2) as t1let2.
  inversion_clear H. fourier.
  
(*+ : quadratic, with real roots; linear; quadratic with complex roots +*)
  inversion_clear sfty as
      [S1 S2 A B C D coeff2 coeff1 coeff0 discr root1 root2 sftytmp |
       A B C coeff2 coeff1 coeff0 sftytmp ];
    cut (0 < A * t^2 + B * t + C);
    [intro; subst; assumption | idtac |
     intro; subst; assumption | idtac];
  unfold a, b, c in coeff0, coeff1, coeff2;
  set (f := (fct_cte A * Rsqr + fct_cte B * id + fct_cte C)%F);
  assert (t^2 = Rsqr t) as Rsqrdef;
  [unfold Rsqr; field | rewrite Rsqrdef; clear Rsqrdef  |
   unfold Rsqr; field | rewrite Rsqrdef; clear Rsqrdef ];
  change  (0 < f t);
  establish_deriv2 f' (fct_cte 2 * fct_cte A * id + fct_cte B)%F f;
  generalize (sftytmp t1let2) as sfty; clear sftytmp t1let2; intro.

  inversion_clear sfty as
      [ [Agt0 [[Dge0pf rootpositions] | Dlt0pf]] | sftyAlt0 ].
  unfold sqrt in root1,root2.
  case_eq (Rcase_abs D).
  intros; apply False_ind; generalize Dge0pf;
  apply (Rgt_not_le _ _ (Rlt_gt _ _ r)).
  intros. rewrite H1 in root1,root2.

(** quadratic with real roots **)
  set (sqrtD := Rsqrt {| nonneg := D; cond_nonneg := Rge_le D 0 r |}).
  change (S1 =(- B - sqrtD) / (2 * A)) in root1.
  change (S2 =(- B + sqrtD) / (2 * A)) in root2.

  assert (A <> 0) as Aneq0.
  apply (Rgt_not_eq A 0 Agt0).

  assert (4*A*A > 0) as AA4gt0.
  setr (4*0).
  setl (4*(A*A)).
  apply (Rmult_gt_compat_l 4).
  prove_sup. fold (Rsqr A).
  apply Rlt_gt.
  apply Rsqr_pos_lt; assumption.
  generalize (Rgt_not_eq _ _ AA4gt0).
  intros AA4neq0. 

  assert (f S1 = 0).
  unfold f, fct_cte, Rsqr, plus_fct, mult_fct, id.
  rewrite root1.
  apply (Rmult_eq_reg_l (4*A*A)).
  setl (- A *B*B + A*(sqrtD*sqrtD) + 4*A*A*C).
  assumption.
  setr 0.
  subst sqrtD. rewrite Rsqrt_Rsqrt.
  simpl.
  rewrite discr. unfold pow. field.
  assumption.
  
  assert (f S2 = 0).
  unfold f, fct_cte, Rsqr, plus_fct, mult_fct, id.
  rewrite root2.
  apply (Rmult_eq_reg_l (4*A*A)).
  setl (- A *B*B + A*(sqrtD*sqrtD) + 4*A*A*C).
  assumption.
  setr 0.
  subst sqrtD. rewrite Rsqrt_Rsqrt.
  simpl.
  rewrite discr. unfold pow. field.
  assumption.

(*** quadratic, with real roots: A>0 ***)
  assert (S1 <= -B/(2*A)).
  rewrite root1.
  apply (Rmult_le_reg_l (2*A)).
  prove_sup. fourier.
  apply (Rplus_le_reg_r B).
  setl (-sqrtD).
  apply Rgt_not_eq. assumption.
  setr  0.
  apply Rgt_not_eq. assumption.
  generalize (Rsqrt_positivity {| nonneg := D; cond_nonneg := Rge_le D 0 r |}).
  intro sqrtDnonneg.
  change (0 <= sqrtD) in sqrtDnonneg.
  fourier.

  assert (-B/(2*A) <= S2).
  rewrite root2.
  apply (Rmult_le_reg_l (2*A)).
  prove_sup. fourier.
  apply (Rplus_le_reg_r B).
  setr sqrtD.
  apply Rgt_not_eq. assumption.
  setl 0.
  apply Rgt_not_eq. assumption.
  generalize (Rsqrt_positivity {| nonneg := D; cond_nonneg := Rge_le D 0 r |}).
  intro sqrtDnonneg.
  change (0 <= sqrtD) in sqrtDnonneg.
  assumption.

  assert (S1 <= S2).
  apply (Rle_trans S1 (- B / (2*A)) S2); assumption.

  assert (forall t, t < -B/(2*A) ->  f' t < 0).
  intros.
  unfold f'.
  unfold fct_cte, id, mult_fct, plus_fct.
  apply (Rplus_lt_reg_r (-B)).
  apply (Rmult_lt_reg_r (/(2*A))).
  apply Rinv_0_lt_compat. fourier.
  setl t0.
  apply Rgt_not_eq. assumption.
  setr (-B/(2*A)).
  apply Rgt_not_eq. assumption.
  assumption.

  (**** quadratic, with real roots, A>0, roots before interval ****)
  assert (forall t, -B/(2*A) < t ->  0 < f' t).
  intros.
  unfold f'.
  unfold fct_cte, id, mult_fct, plus_fct.
  apply (Rplus_lt_reg_r (-B)).
  apply (Rmult_lt_reg_r (/(2*A))).
  apply Rinv_0_lt_compat. fourier.
  setr t0.
  apply Rgt_not_eq. assumption.
  setl (-B/(2*A)).
  apply Rgt_not_eq. assumption.
  assumption.

  (***+ quadratic, with real roots, A>0: roots before interval, roots after interval +***)
  inversion_clear rootpositions as [rootsafterpf | rootsbeforepf].

  (**** quadratic, with real roots, A>0, roots after interval ****)
  generalize (Rgt_lt _ _ rootsafterpf). clear rootsafterpf. intro rootsafterpf.
  
  assert (forall t, t1 < t < S1 -> t < -B/(2*A)).
  intros. inversion_clear H9.
  apply (Rlt_le_trans t0 S1 (-B/(2*A))); try assumption.

  assert (forall t0 : R, t1 < t0 < S1 -> f' t0 < 0).
  intros. apply H7. apply H9. assumption.
  clear H9.
  rewrite <- fe in H10.

  assert (t1 <= t2).
  inversion_clear H. fourier.

  assert (t1 < S1). apply (Rle_lt_trans _ _ _ H9 rootsafterpf).
  rewrite <- H2.
  apply (derive_decreasing_interv t1 S1 f H0 H11 H10).
  inversion_clear H.
  split; fourier.
  split. left. assumption. fourier.
  inversion_clear H. fourier.
  
  assert (forall t, S2 < t < t2 -> -B/(2*A) < t ).
  intros.
  inversion_clear H9.
  apply (Rle_lt_trans (-B/(2*A)) S2 t0); try assumption.

  assert (forall t0 : R, S2 < t0 < t2 -> 0 < f' t0 ).
  intros. apply H8. apply H9. assumption.
  clear H9.
  rewrite <- fe in H10.

  assert (t1 <= t2).
  inversion_clear H. fourier.
  assert (S2 < t2). 
  apply (Rlt_le_trans S2 t1 t2); assumption.

  rewrite <- H3.
  apply (derive_increasing_interv S2 t2 f H0 H11 H10).
  inversion_clear H.
  split. right. reflexivity.
  left. assumption.
  inversion_clear H. split; fourier.
  inversion_clear H. fourier.


  (** quadratic with complex roots **)
  assert (0 < f (-B/(2*A))).
  unfold f, mult_fct, plus_fct, fct_cte, Rsqr, id.
  apply (Rmult_lt_reg_l (4*A)). prove_sup; fourier.
  setl 0.
  setr (- B * B + 4*A*C).
  apply Rgt_not_eq; assumption.
  setl (-0).
  setr (-(B * (B *1) - 4 * A * C)).
  apply Ropp_lt_contravar.
  unfold pow in discr.
  rewrite <- discr. assumption.

  assert (t1 <= t2).
  inversion_clear H. fourier.

  assert (forall t0, t-1 < t0 < -B/(2*A) ->  f' t0 < 0).
  intros. inversion_clear H3 as [trivialbound  belowcenter].
  unfold f'.
  unfold fct_cte, id, mult_fct, plus_fct.
  apply (Rplus_lt_reg_r (-B)).
  apply (Rmult_lt_reg_r (/(2*A))).
  apply Rinv_0_lt_compat. fourier.
  setl t0.
  apply Rgt_not_eq. assumption.
  setr (-B/(2*A)).
  apply Rgt_not_eq. assumption.
  assumption.

  assert (forall t0, -B/(2*A) < t0 < t+1 ->  0 < f' t0).
  intros. inversion_clear H4 as [abovecenter trivialbound ].
  unfold f'.
  unfold fct_cte, id, mult_fct, plus_fct.
  apply (Rplus_lt_reg_r (-B)).
  apply (Rmult_lt_reg_r (/(2*A))).
  apply Rinv_0_lt_compat. fourier.
  setr t0.
  apply Rgt_not_eq. assumption.
  setl (-B/(2*A)).
  apply Rgt_not_eq. assumption.
  assumption.

  generalize (Rtotal_order t (-B/(2*A))). intros.
  inversion_clear H5 as [tltcenter | pos].

  assert (t - 1 < - B / (2 * A)).
  assert (t-1 < t). fourier.
  apply (Rlt_trans _ _ _ H5 tltcenter).

  assert (t - 1 <= t <= - B / (2 * A)).
  split. left. fourier. left. assumption.
  assert (t - 1 <= - B / (2 * A) <= - B / (2 * A)).
  split. left. assumption. right. reflexivity.
  rewrite <- fe in H3.
  generalize (derive_decreasing_interv (t-1) (-B/(2*A))
              f H0 H5 H3 t (-B/(2*A)) H6 H7 tltcenter). intros.
  apply (Rlt_trans 0 (f (- B / (2 * A))) (f t)); try assumption.

  inversion_clear pos as [teqc | tgtc].
  rewrite teqc. assumption.

  assert (- B / (2 * A) < t+1).
  assert (t < t+1). fourier.
  generalize (Rgt_lt _ _ tgtc). intros tgtc2.
  apply (Rlt_trans _ _ _ tgtc2 H5).

  assert (- B / (2 * A) <= t <= t+1).
  split. left. apply Rgt_lt. assumption. fourier.
  assert (- B / (2 * A) <= - B / (2 * A) <= t+1).
  split.  right. reflexivity. left. assumption.
  generalize (Rgt_lt _ _ tgtc). intros tgtc2.

  rewrite <- fe in H4.
  generalize (derive_increasing_interv (-B/(2*A)) (t+1)
                   f H0 H5 H4 (-B/(2*A)) t H7 H6 tgtc2). intros.
  apply (Rlt_trans 0 (f (- B / (2 * A))) (f t)); try assumption.
  
  inversion_clear sftyAlt0 as [Alt0 [Dgt0pf [sfty1 sfty2]]].

  (*** quadratic, with real roots, A<0 ***)
  (***+ quadratic, with real roots, A<0: D>0, D=0 +***)
  
  (**** quadratic, with real roots, A<0, D>0 ****)
  unfold sqrt in root1,root2.
  case_eq (Rcase_abs D).
  intros; apply False_ind. 
  assert (D <= 0) as Dle0; [left; assumption | generalize Dle0].
  apply (Rlt_not_le D 0 Dgt0pf).
  intros. rewrite H1 in root1,root2.

  set (sqrtD := Rsqrt {| nonneg := D; cond_nonneg := Rge_le D 0 r |}).
  change (S1 =(- B - sqrtD) / (2 * A)) in root1.
  change (S2 =(- B + sqrtD) / (2 * A)) in root2.

  assert (A <> 0) as Aneq0.
  apply (Rlt_not_eq A 0 Alt0).

  assert (4*A*A > 0) as AA4gt0.
  setr (4*0).
  setl (4*(A*A)).
  apply (Rmult_gt_compat_l 4).
  prove_sup. fold (Rsqr A).
  apply Rlt_gt.
  apply Rsqr_pos_lt; assumption.
  generalize (Rgt_not_eq _ _ AA4gt0).
  intros AA4neq0. 

  assert (f S1 = 0).
  unfold f, fct_cte, Rsqr, plus_fct, mult_fct, id.
  rewrite root1.
  apply (Rmult_eq_reg_l (4*A*A)).
  setl (- A *B*B + A*(sqrtD*sqrtD) + 4*A*A*C).
  assumption.
  setr 0.
  subst sqrtD. rewrite Rsqrt_Rsqrt.
  simpl.
  rewrite discr. unfold pow. field.
  assumption.
  
  assert (f S2 = 0).
  unfold f, fct_cte, Rsqr, plus_fct, mult_fct, id.
  rewrite root2.
  apply (Rmult_eq_reg_l (4*A*A)).
  setl (- A *B*B + A*(sqrtD*sqrtD) + 4*A*A*C).
  assumption.
  setr 0.
  subst sqrtD. rewrite Rsqrt_Rsqrt.
  simpl.
  rewrite discr. unfold pow. field.
  assumption.

  assert (S2 < -B/(2*A) ).
  rewrite root2.
  apply (Rmult_lt_reg_l (2*(-A))).
  prove_sup. fourier.
  apply (Rplus_lt_reg_r (-B)).
  setl (- sqrtD).
  assumption.
  setr 0.
  assumption.
  generalize (Rsqrt_positivity {| nonneg := D; cond_nonneg := Rge_le D 0 r |}).
  intro sqrtDnonneg.
  change (0 <= sqrtD) in sqrtDnonneg.
  unfold sqrtD, Rsqrt. simpl.
  destruct (Rsqrt_exists D (Rge_le D 0 r)).
  rewrite <- (Ropp_involutive 0).
  apply Ropp_lt_contravar.
  setl 0.
  inversion_clear a0.
  inversion_clear H4.
  assumption.
  apply False_ind.
  rewrite H5 in Dgt0pf.
  rewrite <- H6 in Dgt0pf.
  unfold Rsqr in Dgt0pf.
  assert (0*0 = 0). field. rewrite H4 in Dgt0pf.
  apply (Rlt_irrefl _ Dgt0pf).

  assert (-B/(2*A) < S1).
  rewrite root1.
  apply (Rmult_lt_reg_l (2*(-A))).
  prove_sup. fourier.
  apply (Rplus_lt_reg_r (-B)).
  setr ( sqrtD).
  assumption.
  setl 0.
  assumption.
  generalize (Rsqrt_positivity {| nonneg := D; cond_nonneg := Rge_le D 0 r |}).
  intro sqrtDnonneg.
  change (0 <= sqrtD) in sqrtDnonneg.
  unfold sqrtD, Rsqrt. simpl.
  destruct (Rsqrt_exists D (Rge_le D 0 r)).
  inversion_clear a0.
  inversion_clear H5.
  assumption.
  apply False_ind.
  rewrite H6 in Dgt0pf.
  rewrite <- H7 in Dgt0pf.
  unfold Rsqr in Dgt0pf.
  assert (0*0 = 0). field. rewrite H5 in Dgt0pf.
  apply (Rlt_irrefl _ Dgt0pf).

  assert (S2 < S1).
  apply (Rlt_trans S2 (- B / (2*A)) S1); assumption.

  assert (forall t, t < -B/(2*A) ->  0 < f' t).
  intros. unfold f', fct_cte, id, mult_fct, plus_fct.
  apply (Rplus_lt_reg_r (-B)).
  apply (Rmult_lt_reg_r (/(2*(-A)))).
  apply Rinv_0_lt_compat.
  setl (0*(-A)).
  apply Rmult_lt_compat_r.
  fourier. prove_sup.
  setr (- t0).
  assumption.
  setl (- (- B/(2*A))).
  assumption.
  apply Ropp_lt_contravar.
  assumption.

  assert (forall t, -B/(2*A) < t ->  f' t < 0).
  intros. unfold f', fct_cte, id, mult_fct, plus_fct.
  apply (Rplus_lt_reg_r (-B)).
  apply (Rmult_lt_reg_r (/(2*(-A)))).
  apply Rinv_0_lt_compat.
  setl (2*0).
  apply Rmult_lt_compat_l. prove_sup. fourier.
  setl (-t0).
  assumption.
  setr (- (-B/(2*A))).
  assumption.
  apply Ropp_lt_contravar.
  assumption.

  generalize (Rtotal_order t (-B/(2*A))). intros.
  inversion_clear H9 as [tltcenter | centerpos].
  
  assert (forall t, S2 < t < -B/(2*A) -> t < -B/(2*A)).
  intros. inversion_clear H9. assumption.

  assert (forall t0 : R, S2 < t0 < -B/(2*A) -> 0 < f' t0).
  intros. apply H7. apply H9. assumption.
  clear H7 H9.
  rewrite <- fe in H10.

  rewrite <- H3.
  apply (derive_increasing_interv S2 (-B/(2*A)) f H0 H4 H10).
  inversion_clear H. split. right. reflexivity. left. assumption.
  inversion_clear H. split. left.
  apply (Rlt_le_trans _ _ _ sfty1 H7).
  left. assumption.
  inversion_clear H.
  apply (Rlt_le_trans _ _ _ sfty1 H7).

  inversion_clear centerpos as [teqcenter | tgtcenter].

  rewrite teqcenter in *.
  unfold f, fct_cte, Rsqr, mult_fct, plus_fct, id.
  apply (Rmult_lt_reg_l (4*(-A))). prove_sup. fourier.
  setl 0.
  setr (B^2 - 4*A*C).
  assumption.
  rewrite <- discr. assumption.

  
  assert (forall t, -B/(2*A) < t < S1 -> -B/(2*A) < t ).
  intros.  inversion_clear H9.  assumption.

  assert (forall t0 : R, -B/(2*A) < t0 < S1 ->f' t0 < 0).
  intros. apply H8. apply H9. assumption.
  clear H8 H9.
  rewrite <- fe in H10.

  rewrite <- H2.
  apply (derive_decreasing_interv (-B/(2*A)) S1 f H0 H5 H10).
  inversion_clear H. split. left. apply Rgt_lt. assumption. fourier.
  inversion_clear H. split. left. assumption. right. reflexivity.
  inversion_clear H. fourier.

  (** linear **)
  (**+ linear: B>0, B<0, B=0 +**)
  inversion_clear sfty as
      [Aeq0 [[Bgt0 root] | [[Blt0 root] | [ Beq0  root]]]].

  (*** linear, B>0 ***)
  assert (-C/B < t2). inversion_clear H.
  apply (Rlt_le_trans (-C/B) t t2); try assumption.
  apply (Rlt_le_trans (-C/B) t1 t); try assumption.

  assert (forall t, -C/B < t < t2 -> 0 < f' t).
  intros. 
  unfold f', mult_fct, plus_fct, fct_cte, Rsqr, id. rewrite Aeq0 in *.
  setr B. fourier.

  assert (f (-C/B) = 0).
  unfold f, mult_fct, plus_fct, fct_cte, Rsqr, id. rewrite Aeq0 in *.
  setl 0.
  apply Rgt_not_eq; assumption. reflexivity.

  rewrite <- H3.
  rewrite <- fe in H2.
  apply (derive_increasing_interv (-C/B) t2 f H0 H1 H2 (-C/B) t); try assumption.
  split. right. reflexivity. left. assumption.
  inversion_clear H. split. left.
  apply (Rlt_le_trans (-C/B) t1 t); try assumption.
  assumption.
  inversion_clear H.
  apply (Rlt_le_trans (-C/B) t1 t); try assumption.
  

  (*** linear, B<0 ***)
  assert (t1 < -C/B). inversion_clear H.
  apply (Rle_lt_trans t1 t (-C/B)); try assumption.
  apply (Rle_lt_trans t t2 (-C/B)); try assumption.

  assert (forall t, t1 < t < -C/B -> f' t < 0 ).
  intros. 
  unfold f', mult_fct, plus_fct, fct_cte, Rsqr, id. rewrite Aeq0 in *.
  setl B. fourier.

  assert (f (-C/B) = 0).
  unfold f, mult_fct, plus_fct, fct_cte, Rsqr, id. rewrite Aeq0 in *.
  setl 0.
  apply Rlt_not_eq; assumption. reflexivity.

  rewrite <- H3.
  rewrite <- fe in H2.
  apply (derive_decreasing_interv t1 (-C/B) f H0 H1 H2 t (-C/B));
    try assumption.
  inversion_clear H.
  split. assumption. left. 
  apply (Rle_lt_trans t t2 (-C/B)); try assumption.
  inversion_clear H.
  split. left.
  apply (Rle_lt_trans t1 t2 (-C/B)); try assumption.
  fourier. right. reflexivity.
  inversion_clear H. 
  apply (Rle_lt_trans t t2 (-C/B)); try assumption.

  (*** linear, B=0 ***)
  unfold f, mult_fct, plus_fct, fct_cte, Rsqr, id.
  rewrite Aeq0, Beq0 in *.
  setr C.
  fourier.

Qed.


(* This function defines a trajectory that describes altitude over
time, following a parabolic trajectory until it reaches a target
velocity vt, and then staying at that velocity and changing altitude
at a constant rate.  The initial altitude at t=0 is z, and v is the
linear coefficient for the parabolic path, and the aircraft
accelerates towards target velocity vt with acceleration a.

Note that if 0 <= (vt-v)/a, v is the velocity at time t=0. If (vt-v)/a
<= 0, the vertical velocity at t=0 is actually vt and there is no
acceleration in the path.
So: 

K(t) = a/2*t^2 + v*t + z                   when 0 <= t < max(0, (vt-v)/a) 
       vt*t - (vt-v)/2*max(0,(vt-v)/a) + z when max(0, (vt-v)/a) <= t


a/2*max(0,(vt-v)/a)^2 + v max(0, (vt-v)/a) + z = ?

(vt^2 - v^2))/2a + z = ?
       

K'(t) = a*t + v = vt at [t = (vt-v)/a]

reaches value 
= a/2 t^2 + v t + z 
= a/2 (vt-v)^2/a^2 + v (vt-v)/a + z
= (vt^2+v^2 - 2vt v)/2a + 2v (vt-v)/2a + z 
= (vt^2+v^2 - 2vt v + 2v vt-2 v^2)/2a + z 
= (vt^2 - v^2)/2a + z

so the linear part of the equation is: 
= vt (t-(vt-v)/a) + (vt^2 - v^2)/2a + z
= vt t + 2 (- vt^2 + vt v)/2a + (vt^2 - v^2)/2a + z
= vt t + (- vt^2 + 2 vt v - v^2)/2a + z
= vt t - ( vt^2 - 2 vt v + v^2)/2a + z
= vt t - ( vt - v)^2/2a + z
= vt t - tl*(vt-v)/2 + z
this is only true when (vt-v)/a >= 0. If (vt-v)/a < 0, vt + z


 max(0,(vt-v))^2/2*a <= t *)

Definition K aa ab v vt z t :=
  let a := match total_order_T vt v with
           | inleft _ => (* vt<=v *) aa
           | inright _ => (* vt>v *) ab
           end in
  let Q := mkcoeff (a/2) v z in
  let tl := (vt-v)/a in
  let L := mkcoeff 0 vt (-tl*(vt-v)/2 + z) in
  match total_order_T t tl with
  | inleft _ => (J Q t) (*le*)
  | inright _ => (J L t) (*gt *)
  end.


Inductive Φ aa1 ab1 v1 vt1 z1 aa2 ab2 v2 vt2 z2 hp tb te : Prop := 
| vsafe : forall Q1 Q2 L1 L2 t1 t2 a1 a2,
    aa1 < 0 -> ab1 > 0 ->
    aa2 < 0 -> ab2 > 0 ->
    a1 = match total_order_T vt1 v1 with
         | inleft _ => aa1
         | inright _ => ab1
         end -> 
    a2 = match total_order_T vt2 v2 with
         | inleft _ => aa2
         | inright _ => ab2
         end -> 
    Q1 = mkcoeff (a1/2) v1 z1 ->
    Q2 = mkcoeff (a2/2) v2 z2 ->
    t1 = (vt1-v1)/a1 ->
    t2 = (vt2-v2)/a2 ->
    L1 = mkcoeff 0 vt1 (-t1*(vt1-v1)/2 + z1) ->
    L2 = mkcoeff 0 vt2 (-t2*(vt2-v2)/2 + z2) ->
          (Γ Q1 Q2 hp tb (Rmin te (Rmin t1 t2))) /\
          (Γ L1 L2 hp (Rmax tb (Rmax t1 t2)) te) /\
          (t1 > t2 -> Γ Q1 L2 hp (Rmax tb (Rmin t1 t2))
                                                  (Rmin te (Rmax t1 t2))) /\
          (t1 < t2 -> Γ L1 Q2 hp (Rmax tb (Rmin t1 t2))
                                                  (Rmin te (Rmax t1 t2))) ->
          Φ aa1 ab1 v1 vt1 z1 aa2 ab2 v2 vt2 z2 hp tb te.


Theorem safely_separated_trajectory_interval_above: forall aa1 ab1 v1 vt1 z1 aa2 ab2 v2 vt2 z2 hp tb te t,
               tb <= t <= te ->
               Φ aa1 ab1 v1 vt1 z1 aa2 ab2 v2 vt2 z2 hp tb te ->
               hp < K aa1 ab1 v1 vt1 z1 t - K aa2 ab2 v2 vt2 z2 t.
Proof.
  intros.
  inversion_clear H0 as
      [Q1 Q2 L1 L2 t1 t2 a1 a2 aa1lt0 ab1gt0 aa2lt0 ab2gt0 a1def a2def Q1def Q2def t1def t2def L1def L2def
          [QQ [LL [QL LQ]]]].
  unfold K.
  rewrite <- a1def.
  rewrite <- a2def.
  rewrite <- Q1def.
  rewrite <- Q2def.
  rewrite <- t1def.
  rewrite <- t2def.
  rewrite <- L1def.
  rewrite <- L2def.
  inversion_clear H as [tblet tlete].
  destruct (total_order_T t t1) as [p | tgtRmax1];
    destruct (total_order_T t t2) as [q | tgtRmax2];
  try inversion_clear p as [tltRmax1 | teqRmax1 ];
  try inversion_clear q as [tltRmax2 | teqRmax2 ].
  clear QL LQ LL.
  apply (safely_separated_second_order_polynomial_interval _ _ _
                        tb (Rmin te (Rmin t1 t2))).
  split. assumption.
  unfold Rmin.
  destruct (Rle_dec t1 t2).
  destruct (Rle_dec te t1).
  assumption.
  left. assumption.

  destruct (Rle_dec te t2).
  assumption. left. assumption.
  assumption.
  
  clear QL LQ LL.
  apply (safely_separated_second_order_polynomial_interval _ _ _
                                tb (Rmin te (Rmin t1 t2))).
  split. assumption. 
  unfold Rmin.
  destruct (Rle_dec t1 t2).
  destruct (Rle_dec te t1).
  assumption.
  left. assumption.
  destruct (Rle_dec te t2).
  assumption.
  rewrite teqRmax2.
  right. reflexivity.
  assumption.

  clear QL LQ LL.
  apply (safely_separated_second_order_polynomial_interval _ _ _
                                  tb (Rmin te (Rmin t1 t2))).
  split. assumption.
  unfold Rmin.
  destruct (Rle_dec t1 t2).
  destruct (Rle_dec te t1).
  assumption. rewrite teqRmax1.
  right. reflexivity.
  destruct (Rle_dec te t2).
  assumption. left. assumption.
  assumption.

  clear QL LQ LL.
  apply (safely_separated_second_order_polynomial_interval _ _ _
                              tb (Rmin te (Rmin t1 t2))).
  split. assumption.
  unfold Rmin.
  destruct (Rle_dec t1 t2).
  destruct (Rle_dec te t1).
  assumption.
  rewrite teqRmax1. 
  right. reflexivity.
  destruct (Rle_dec te t2).
  assumption.
  rewrite teqRmax2. right. reflexivity.
  assumption.

  clear LQ LL QQ.
  cut (t1 > t2). intros.
  generalize (QL H). clear QL. intros QL.
  apply (safely_separated_second_order_polynomial_interval _ _ _
                       (Rmax tb (Rmin t1 t2)) (Rmin te (Rmax t1 t2))).
  split.
  unfold Rmin.
  destruct (Rle_dec t1 t2).
  apply False_ind; apply (Rgt_not_le _ _ H r). clear n.
  unfold Rmax.
  destruct (Rle_dec tb t2).
  left. assumption.
  assumption.

  unfold Rmax, Rmin.
  destruct (Rle_dec t1 t2).
  destruct (Rle_dec te t2). assumption.
  apply False_ind; apply (Rgt_not_le _ _ H r).
  destruct (Rle_dec te t1). assumption.
  left. assumption.
  assumption.

  clear QL.
  apply Rlt_gt.
  apply (Rlt_trans _ t _).
  apply Rgt_lt. assumption. assumption.

  clear LQ LL QQ.
  rewrite teqRmax1 in tgtRmax2.
  generalize (QL tgtRmax2). clear QL. intros QL.
  apply (safely_separated_second_order_polynomial_interval _ _ _
                                 (Rmax tb (Rmin t1 t2)) (Rmin te (Rmax t1 t2))).
  split.
  unfold Rmin at 1.
  destruct (Rle_dec t1 t2).
  unfold Rmax.
  destruct (Rle_dec tb t1).
  right. symmetry. assumption.
  clear n. assumption.
  unfold Rmax.
  destruct (Rle_dec tb t2).

  left. rewrite teqRmax1.
  apply Rgt_lt. assumption.
  assumption.
  
  unfold Rmax.
  destruct (Rle_dec t1 t2).
  unfold Rmin.
  destruct (Rle_dec te t2).
  assumption.
  rewrite teqRmax1. assumption.
  unfold Rmin.
  destruct (Rle_dec te t1).
  assumption. rewrite teqRmax1. right.
  reflexivity.
  assumption.
(**************)

  clear QL LL QQ.
  cut (t1 < t2). intros.
  generalize (LQ H). clear LQ H. intros LQ.
  apply (safely_separated_second_order_polynomial_interval _ _ _
                            (Rmax tb (Rmin t1 t2)) (Rmin te (Rmax t1 t2))).
  split.
  unfold Rmin at 1.
  destruct (Rle_dec t1 t2).
  unfold Rmax.
  destruct (Rle_dec tb t1).
  left.  assumption.
  assumption.
  unfold Rmax.
  destruct (Rle_dec tb t2).
  apply False_ind.
  apply n.
  left.
  apply (Rlt_trans _ t).
  apply Rgt_lt. assumption.
  assumption. assumption.

  unfold Rmax.
  destruct (Rle_dec t1 t2).
  unfold Rmin.
  destruct (Rle_dec te t2).
  assumption. left. assumption.
  unfold Rmin.
  destruct (Rle_dec te t1).
  assumption. left. 
  apply False_ind. apply n.
  left.
  apply (Rlt_trans _ t).
  apply Rgt_lt. assumption.
  assumption.
  assumption.

  clear LQ.
  apply (Rlt_trans _ t).
  apply Rgt_lt. assumption.
  assumption.

  clear QL LL QQ.
  rewrite teqRmax2 in tgtRmax1.
  generalize (LQ (Rlt_gt _ _ tgtRmax1)). clear LQ. intros LQ.
  apply (safely_separated_second_order_polynomial_interval _ _ _
                           (Rmax tb (Rmin t1 t2)) (Rmin te (Rmax t1 t2))).
  split.
  unfold Rmin at 1.
  destruct (Rle_dec t1 t2).
  unfold Rmax.
  destruct (Rle_dec tb t1).
  rewrite teqRmax2. assumption.
  assumption.
  unfold Rmax.
  destruct (Rle_dec tb t2).
  apply False_ind. apply n.
  left.
  apply Rgt_lt. assumption.
  assumption.
  
  unfold Rmax at 1.
  destruct (Rle_dec t1 t2).
  unfold Rmin.
  destruct (Rle_dec te t2). assumption.
  right. assumption.
  unfold Rmin.
  destruct (Rle_dec te t1). assumption.
  apply False_ind. apply n.
  left.
  apply Rgt_lt. assumption.
  assumption.

(****************************)  
  clear LQ QL QQ.
  apply (safely_separated_second_order_polynomial_interval _ _ _
                                  (Rmax tb (Rmax t1 t2)) te).
  split.
  unfold Rmax.
  destruct (Rle_dec t1 t2).
  destruct (Rle_dec tb t2).
  left.
  apply Rgt_lt. assumption. assumption.
  destruct (Rle_dec tb t1).
  left.
  apply Rgt_lt. assumption. assumption. assumption.

  assumption.
Qed.

Ltac assume n := generalize n; intro.


(* Collects geometric and dynamic information about aircraft motion. *)

(* For this definition, we are continuous during the interior each
maneuver, but the point at the beginning of each maneuver is not
necessarily continuous on either side. We need to create a definition
for continuity "from the right" which shouldn't be to hard *)

Inductive Path (z v a :R->R) :=
| pth_intro :
    forall (dvp : derivable z) (contz: continuity z)
           (dpeqv : derive z dvp = v)
           (dvv : derivable v) (contv: continuity v)
           (dveqa : derive v dvv = a)
           (conta: continuity a), Path z v a.

Record Objective  :=
  {
    vmax:R; vmin:R; aa:R; amax:R; amin:R; ab:R;
    vminlevmax : vmin<=vmax;
    aminleaa : amin <= aa;
    aalt0 : aa < 0;
    zltab : 0 < ab;
    ableamax : ab <= amax
  }.


Inductive Maneuver {z v a} t1 t2 (P: Path z v a) (B:Objective) :=
| mnv_intro : forall 
           (interval : t1 <= t2)
           (vabove : forall t, t1<=t<t2 -> (vmax B) < v t -> (amin B) <= a t <= (aa B))
           (vatupper : forall t, t1<=t<t2 -> v t = (vmax B) -> (amin B) <= a t <= 0)
           (vwithin: forall t, t1<=t<t2 -> (vmin B) < v t < (vmax B)  -> (amin B) <= a t <= (amax B))
           (vatlower : forall t, t1<=t<t2 -> v t = (vmin B) -> 0 <= a t <= (amax B))
           (vbelow : forall t, t1<=t<t2 -> v t < (vmin B) -> (ab B) <= a t <= (amax B)),
                Maneuver t1 t2 P B.

Inductive TailManeuver {z v a} t1 (P: Path z v a) (B:Objective) :=
| tmnv_intro : forall
           (mnv : forall t2, Maneuver t1 t2 P B),
                TailManeuver t1 P B.

(*
The 'ua' ltac is short for "unpack assumptions."

Assumes type starts with the following:
forall t1 t2 z v a (P: Path z v a) B (M: Maneuver t1 t2 P B)...
*)
Ltac ua :=
  intros t1 t2 z v a P B M;
  inversion P;
  inversion M as [interval 
           vabove 
           vatupper 
           vwithin
           vatlower 
           vbelow];
  case_eq B;
  intros vmax vmin aa amax amin ab vminlevmax
         aminleaa aalt0 zltab ableamax Bdef;
  rewrite Bdef in vabove, vatupper, vwithin, vatlower, vbelow (*, M*);
  simpl in *(*; clear Bdef*).

Lemma pilot_model_maintains_lower_bound :
  forall {t1 t2 z v a} (P: Path z v a) B (M: Maneuver t1 t2 P B)
         x, t1 <= x < t2 -> (vmin B) <= v x ->
            forall y, t1 <= y < t2 -> x < y -> (vmin B) <= v y.
Proof.
  ua.
  intros x [t1lex xltt2] vminltvx y [t1ley yltt2] xlty.

  apply Rnot_lt_le.
  intro.

  set (C := (vmin + v y)/2).
  assert (C < vmin) as Cltvmin. unfold C;
  apply (Rmult_lt_reg_l 2); try prove_sup;
  setl (vmin + v y); Radd (-vmin); setr vmin; setl (v y); assumption.

  assert (v y < C) as vyltC. unfold C.
  apply (Rmult_lt_reg_l 2); try prove_sup;
  setr (vmin + v y); Radd (-v y); setr vmin; setl (v y); assumption.
  
  set (f := (fun x => v x - C)).
  assert (continuity f) as contf. unfold f.
  assume contv. reg.
  assert (f y < 0) as fyltz. unfold f.
  Radd C.
  setl (v y).
  setr C. assumption.
  assert (0 < f x) as zltfx. unfold f. Radd C.
  setr (v x). setl C. fourier.
  assert (f x >= 0) as zlefx. left. assumption.
  generalize (last_leg_drop f x y contf xlty zlefx fyltz) as llr. intros.
  inversion_clear llr as [p [[xltp plty] [flhs below]]].
  assert (v p = C) as lhs.
  Radd (-C). setl (v p - C). setr 0. assumption.

  generalize (MVT_cor1 v p y dvv plty) as mvt. intros.
  inversion_clear mvt as [c [derivvc [pltc clty]]].
  assert (v y - v p < 0) as vymvplt0.
  rewrite lhs.
  Radd C.
  setr C.
  setl (v y).
  assumption.
  
  rewrite derivvc in vymvplt0.
  assert (0 < y-p).
  Radd p.
  setl p.
  setr y. assumption.
  assert (derive_pt v c (dvv c) < 0).
  apply (Rmult_lt_reg_r (y-p)); try assumption.
  setr 0. assumption.

  assert (p < c < y).
  split. assumption.
  assumption.
  generalize (below c H2). intros.

  assert (v c < vmin) as vcltvmin. 
  apply (Rlt_trans (v c) C vmin).
  Radd (-C). setr 0. setl (v c - C). assumption.
  assumption.

  assert (t1 <= c <t2) as cinterval; [split; fourier | idtac].
  generalize (vbelow c cinterval vcltvmin) as accel. intros. clear below.
  inversion_clear accel as [ableac acleamax].
  rewrite <- dveqa in ableac.
  unfold derive in ableac.
  assert (0 < derive_pt v c (dvv c)).
  assume zltab. fourier.
  clear ableac acleamax.
  eapply Rlt_asym.
  apply H4. apply H1.
Qed.

Lemma pilot_model_maintains_upper_bound:
  forall {t1 t2 z v a} (P: Path z v a) B (M: Maneuver t1 t2 P B)
         x, t1 <= x < t2 -> v x <= vmax B ->
            forall y, t1 <= y < t2 -> x < y -> v y <= vmax B.
Proof.
  ua.

  intros x [t1lex xltt2] vxlevmax y [t1ley yltt2] xlty.

  apply Rnot_lt_le.
  intro.

  set (C := (vmax + v y)/2).
  assert (vmax < C) as vmaxltC. unfold C;
  apply (Rmult_lt_reg_l 2); try prove_sup;
  setr (vmax + v y); Radd (-vmax); setl vmax; setr (v y); assumption.

  assert (C < v y) as Cltvy. unfold C.
  apply (Rmult_lt_reg_l 2); try prove_sup;
  setl (vmax + v y); Radd (-v y); setl vmax; setr (v y); assumption.
  
  set (f := (fun x => v x - C)).
  assert (continuity f) as contf. unfold f.
  assume contv. reg.
  assert (0 < f y) as zltfy. unfold f.
  Radd C.
  setr (v y).
  setl C. assumption.
  assert (f x < 0) as fxltz. unfold f. Radd C.
  setl (v x). setr C. fourier.
  assert (f x <= 0 ) as fxle0. left. assumption.
  generalize (last_leg_rise f x y contf xlty fxle0 zltfy ) as llr. intros.
  inversion_clear llr as [p [[xltp plty] [flhs above]]].
  assert (v p = C) as lhs.
  Radd (-C). setl (v p - C). setr 0. assumption.

  generalize (MVT_cor1 v p y dvv plty) as mvt. intros.
  inversion_clear mvt as [c [derivvc [pltc clty]]].
  assert (0 < v y - v p ) as vymvygt0.
  rewrite lhs.
  Radd C.
  setl C.
  setr (v y).
  assumption.
  
  rewrite derivvc in vymvygt0.
  assert (0 < y-p).
  Radd p.
  setl p.
  setr y. assumption.
  assert (0 < derive_pt v c (dvv c)).
  apply (Rmult_lt_reg_r (y-p)); try assumption.
  setl 0. assumption.

  assert (p < c < y).
  split. assumption.
  assumption.
  generalize (above c H2). intros.

  assert (v c > vmax) as vcgtvmax. apply Rlt_gt.
  apply (Rlt_trans vmax C (v c)). assumption.
  Radd (-C). setl 0. setr (v c - C). assumption.

  assert (t1 <= c <t2) as cinterval; [split; fourier | idtac].
  generalize (vabove c cinterval vcgtvmax) as accel. intros. clear above.
  inversion_clear accel as [aminleac acleaa].
  rewrite <- dveqa in acleaa.
  unfold derive in acleaa.
  assert (derive_pt v c (dvv c) < 0).
  assume aalt0.  fourier.
  clear acleaa aminleac.
  eapply Rlt_asym.
  apply H4. apply H1.
Qed.

Theorem pilot_model_maintains_vertical_compliance :
  forall {t1 t2 z v a} (P: Path z v a) B (M: Maneuver t1 t2 P B)
    x, t1 <= x < t2 -> vmin B <= v x <= vmax B ->
       forall y, t1 <= y < t2 -> x < y -> vmin B <= v y <= vmax B.
Proof.
  ua.
  intros.
  inversion_clear H0.
  rewrite Bdef in M.
  split.
  apply (pilot_model_maintains_lower_bound P ({|
         vmax := vmax;
         vmin := vmin;
         aa := aa;
         amax := amax;
         amin := amin;
         ab := ab;
         vminlevmax := vminlevmax;
         aminleaa := aminleaa;
         aalt0 := aalt0;
         zltab := zltab;
         ableamax := ableamax |}) M x H H3 y H1 H2).
  apply (pilot_model_maintains_upper_bound P ({|
         vmax := vmax;
         vmin := vmin;
         aa := aa;
         amax := amax;
         amin := amin;
         ab := ab;
         vminlevmax := vminlevmax;
         aminleaa := aminleaa;
         aalt0 := aalt0;
         zltab := zltab;
         ableamax := ableamax |}) M x H H4 y H1 H2).
Qed.

Lemma pilot_model_accel_below :
  forall {t1 t2 z v a} (P: Path z v a) B (M: Maneuver t1 t2 P B)
         x, t1 <= x < t2 -> v x < vmin B ->
            forall y, t1 <= y < t2 -> x < y -> v y < vmin B ->
                      (ab B) * (y - x) <= v y - v x.
Proof.
  ua.
  generalize (pilot_model_maintains_lower_bound P B M) as pilot_model_maintains_lower_bound_traj. intro.
  rewrite Bdef in pilot_model_maintains_lower_bound_traj. simpl in pilot_model_maintains_lower_bound_traj.
  intros x xinterval vxlevmin y yinterval xlty.
  inversion xinterval as [t1ley yltt2].
  inversion yinterval as [t1lex xltt2].
  generalize contv as contv0; intro.
  rewrite <- dpeqv in contv0.
  generalize conta as conta0; intro.
  rewrite <- dveqa in conta0.

  set (vl := (fct_cte ab * id)%F).
  assert (continuity vl) as contvl. unfold vl. reg.
  establish_deriv2 vl' (fct_cte ab)%F vl.
  rename H into derivvl.
  rename fe into dvleqvl'.
  assert (continuity vl') as contlv'. unfold vl'. reg.
  rewrite <- dvleqvl' in contlv'.

  set (afun := (mkC1 conta0)).
  set (alfun := (mkC1 contlv')).
  
  generalize (RiemannInt_P32 afun x y) as vintegr. intros.
  generalize (FTC_Riemann afun vintegr) as vintval. intros.

  generalize (RiemannInt_P32 alfun x y) as vlintegr. intros.
  generalize (FTC_Riemann alfun vlintegr) as vlintval. intros.

  simpl in *. unfold vl, fct_cte, id, mult_fct in vlintval.
  rewrite <- vintval.
  setl (ab* y - ab * x).
  rewrite <- vlintval.
  
  apply RiemannInt_P19.
  left. assumption.
  intros. unfold vl, fct_cte, mult_fct, id in dvleqvl'.
  rewrite dvleqvl'.
  rewrite dveqa.
  unfold vl', fct_cte.
  apply vbelow.
  inversion H0. split; fourier.

  assert (v x0 <= v y) as vx0levy.
  apply Rnot_lt_le. intro vyltvx0.
  inversion_clear H0 as [xltx0 x0lty].
  generalize (MVT_cor1 v x0 y dvv x0lty) as mvt. intro.
  inversion_clear mvt as [c [dpvc x0ltclty]].
  inversion_clear x0ltclty as [x0ltc clty].
  assert (v y - v x0 < 0) as vxmvx0lt0. fourier.
  rewrite dpvc in vxmvx0lt0.
  assert (derive_pt v c (dvv c) < 0) as vxmvx0lt00.
  apply (Rmult_lt_reg_r (y-x0)). fourier.
  setr 0. assumption. clear vxmvx0lt0 dpvc.
  generalize (Rtotal_order (v c) vmin) as vcto. intros.
  inversion_clear vcto as [vcltvmin | vcgeqvmin].
  assert (t1 <= c <t2) as cinterval; [split; fourier | idtac].
  generalize (vbelow c cinterval vcltvmin) as acrel. intros.
  inversion_clear acrel as [ableac acleamax].
  change ((derive v dvv) c < 0) in vxmvx0lt00.
  rewrite dveqa in vxmvx0lt00.
  assert (0 <= a c) as zleac. assume zltab. fourier.
  generalize zleac.
  apply Rlt_not_le. assumption.
  assert (vmin <= v c) as vminlevc.
  inversion_clear vcgeqvmin as [vceqvmin | vcgtvmin].
  right. symmetry. assumption. left. assumption. clear vcgeqvmin.
  assert (t1 <= c <t2) as cinterval; [split; fourier | idtac].
  generalize (pilot_model_maintains_lower_bound_traj c cinterval vminlevc y yinterval clty) as vminlevy. intros.
  apply (Rlt_not_le vmin (v y)). assumption. assumption.
  fourier.
  
Qed.


Lemma pilot_model_accel_above :
    forall {t1 t2 z v a} (P: Path z v a) B (M: Maneuver t1 t2 P B)
           x, t1 <= x < t2 -> vmax B < v x ->
              forall y, t1 <= y < t2 -> x < y -> vmax B < v y ->
                        v y - v x <= (aa B) * (y - x).
Proof.
  ua.
  generalize (pilot_model_maintains_upper_bound P B M) as pilot_model_maintains_upper_bound_traj. intro.
  rewrite Bdef in pilot_model_maintains_upper_bound_traj. simpl in pilot_model_maintains_upper_bound_traj.
  intros x xinterval vmaxltvx y yinterval xlty vmaxltvy.
  inversion xinterval as [t1ley yltt2].
  inversion yinterval as [t1lex xltt2].
  
  generalize contv as contv0; intro.
  rewrite <- dpeqv in contv0.
  generalize conta as conta0; intro.
  rewrite <- dveqa in conta0.

  set (vl := (fct_cte aa * id)%F).
  assert (continuity vl) as contvl. unfold vl. reg.
  establish_deriv2 vl' (fct_cte aa)%F vl.
  rename H into derivvl.
  rename fe into dvleqvl'.
  assert (continuity vl') as contlv'. unfold vl'. reg.
  rewrite <- dvleqvl' in contlv'.
  set (afun := (mkC1 conta0)).
  set (alfun := (mkC1 contlv')).
  
  generalize (RiemannInt_P32 afun x y) as vintegr. intros.
  generalize (FTC_Riemann afun vintegr) as vintval. intros.

  generalize (RiemannInt_P32 alfun x y) as vlintegr. intros.
  generalize (FTC_Riemann alfun vlintegr) as vlintval. intros.

  simpl in *. unfold vl, fct_cte, id, mult_fct in vlintval.
  rewrite <- vintval.
  setr (aa* y - aa * x).
  rewrite <- vlintval.
  
  apply RiemannInt_P19.
  left. assumption.
  intros. unfold vl, fct_cte, mult_fct, id in dvleqvl'.
  rewrite dvleqvl'.
  rewrite dveqa.
  unfold vl', fct_cte.
  apply vabove. inversion H. split ; fourier.

  assert (v y <= v x0) as vx0levy.
  apply Rnot_lt_le. intro vyltvx0.
  inversion_clear H as [xltx0 x0lty].
  generalize (MVT_cor1 v x0 y dvv x0lty) as mvt. intro.
  inversion_clear mvt as [c [dpvc x0ltclty]].
  inversion_clear x0ltclty as [x0ltc clty].
  assert (0 < v y - v x0) as vxmvx0lt0. fourier.
  rewrite dpvc in vxmvx0lt0.
  assert (0 < derive_pt v c (dvv c) ) as vxmvx0lt00.
  apply (Rmult_lt_reg_r (y-x0)). fourier.
  setl 0. assumption. clear vxmvx0lt0 dpvc.
  generalize (Rtotal_order vmax (v c)) as vcto. intros.
  inversion_clear vcto as [vcltvmin | vcgeqvmin].
  assert (t1 <= c <t2) as cinterval; [split; fourier | idtac].
  generalize (vabove c cinterval vcltvmin) as acrel. intros.
  inversion_clear acrel as [ableac acleamax].
  change (0 < (derive v dvv) c) in vxmvx0lt00.
  rewrite dveqa in vxmvx0lt00.
  assert (0 <= a c) as zleac. fourier. generalize zleac.
  apply Rlt_not_le. assume aalt0. fourier.
  assert (v c <= vmax) as vminlevc.
  inversion_clear vcgeqvmin as [vceqvmin | vcgtvmin].
  right. symmetry. assumption. left. assumption. clear vcgeqvmin.
  assert (t1 <= c <t2) as cinterval; [split; fourier | idtac].
  generalize (pilot_model_maintains_upper_bound_traj c cinterval vminlevc y yinterval clty) as vminlevy. intros.
  apply (Rlt_not_le (v y) vmax). assumption. assumption.
  fourier.
  
Qed.

Lemma pilot_model_accel_below_limit :
  forall {t1 t2 z v a} (P: Path z v a) B (M: Maneuver t1 t2 P B)
         x, t1 <= x < t2 -> v x < vmin B ->
            forall y, t1 <= y < t2 -> 0 < y - x < (vmin B - v x) / (ab B) ->
                      (ab B) * (y - x) <= v y - v x.
Proof.
  ua.
  generalize (pilot_model_accel_below P B M) as pilot_model_accel_below_traj. intro.
  rewrite Bdef in pilot_model_accel_below_traj. simpl in pilot_model_accel_below_traj.
  intros x xinterval vxltvmxn y yinterval [zltymx ymxlttt].
  inversion xinterval as [t1ley yltt2].
  inversion yinterval as [t1lex xltt2].

  generalize (Rtotal_order (v y) vmin) as vyvminto. intros.
  assert (v y < vmin \/ v y >= vmin) as vyvminrel.
  inversion_clear vyvminto as [vyltvmin | [vyeqvmin | vygtvmin]].
  left. assumption. right. right. assumption. right. left. assumption.
  clear vyvminto.
  inversion_clear vyvminrel as [vyltvmin | vygevmin ].
  apply pilot_model_accel_below_traj. split; fourier.
  assumption. split; fourier. fourier. assumption.
  apply Rge_le in vygevmin.

  set (f := (fun q => v q - vmin)).
  assert (continuity f) as contf. unfold f.
  assume contv. reg.
  assert (f x < 0) as fxlt0. unfold f. fourier.
  assert (x < y) as xlty. fourier.
  assert (f y >= 0) as fyge0. unfold f. fourier.
  generalize (first_leg_rise f x y contf xlty fxlt0 fyge0) as flr.
  intros. inversion_clear flr as [p [[xltp pley] [fpeq0 rst]]].
  unfold f in *.

  assume zltab. (*rename H0 into zltab0.*)
  apply (Rle_trans _ (vmin - v x) _).
  left. apply (Rmult_lt_reg_l (/ab)).
  apply Rinv_0_lt_compat. assume zltab. assumption.
  setl (y - x).
  intro. rewrite H in zltab0. apply (Rlt_irrefl 0). assumption.
  setr ((vmin - v x) / ab).
  intro. rewrite H in zltab0. apply (Rlt_irrefl 0). assumption.
  assumption.
  Radd (v x). setl vmin. setr (v y).
  assumption.
Qed.

Lemma pilot_model_accel_at_lower_limit :
  forall {t1 t2 z v a} (P: Path z v a) B (M: Maneuver t1 t2 P B)
         x, t1 <= x < t2 -> v x < vmin B ->
            forall y, t1 <= y < t2 -> 0 < y - x /\ y - x = ((vmin B) - v x) / (ab B) ->
                      (ab B) * (y - x) <= v y - v x.
Proof.
  ua.
  generalize (pilot_model_accel_below_limit P B M) as pilot_model_accel_below_limit_traj. intro.
  rewrite Bdef in pilot_model_accel_below_limit_traj. simpl in pilot_model_accel_below_limit_traj.
  intros x xinterval vxltvmin y yinterval [zltymx ymxlttt].
  inversion xinterval as [t1ley yltt2].
  inversion yinterval as [t1lex xltt2].

  intros.
  Radd (v x).
  setr (v y).
  set (fll := (fct_cte ab * (id - fct_cte x) + fct_cte (v x))%F).
  assert (continuity fll) as contfll. unfold fll. reg.
  change (fll y <= v y).
  assume contv.
  apply limpoint; try assumption. (* clear H1. *)
  exists x. split. fourier.
  intros x0 xltx0lty.
  unfold fll, fct_cte, mult_fct, id, minus_fct, plus_fct.
  Radd (- v x). setl (ab * (x0 - x)). setr (v x0 - v x).
  inversion_clear xltx0lty as [xltx0 x0lty]. 
  apply pilot_model_accel_below_limit_traj; try assumption.
  split; fourier.
  split. fourier.
  rewrite <- ymxlttt.
  Radd x. setl x0. setr y.
  assumption.
Qed.

Lemma pilot_model_accel_upto_limit :
  forall {t1 t2 z v a} (P: Path z v a) B (M: Maneuver t1 t2 P B)
         x, t1 <= x < t2 -> v x < vmin B ->
            forall y, t1 <= y < t2 -> 0 < y - x <= (vmin B - v x) / (ab B) ->
                      (ab B) * (y - x) <= v y - v x.
Proof.
  ua.
  generalize (pilot_model_accel_below_limit P B M) as pilot_model_accel_below_limit_traj. intro.
  rewrite Bdef in pilot_model_accel_below_limit_traj. simpl in pilot_model_accel_below_limit_traj.
  generalize (pilot_model_accel_at_lower_limit P B M) as pilot_model_accel_at_lower_limit_traj. intro.
  rewrite Bdef in pilot_model_accel_at_lower_limit_traj. simpl in pilot_model_accel_at_lower_limit_traj.
  intros x xinterval vxltvmin y yinterval [zltymx [ymxltvm | ymxeqvm]].
  inversion xinterval as [t1ley yltt2].
  inversion yinterval as [t1lex xltt2].

  apply pilot_model_accel_below_limit_traj; try assumption.
  split; try assumption.
  apply pilot_model_accel_at_lower_limit_traj; try assumption.
  split. assumption. assumption.
Qed.

Lemma pilot_model_accel_above_limit :
  forall {t1 t2 z v a} (P: Path z v a) B (M: Maneuver t1 t2 P B)
         x, t1 <= x < t2 -> vmax B < v x ->
            forall y, t1 <= y < t2 -> 0 < y - x < (vmax B - v x) / (aa B) ->
                      v y - v x <= (aa B) * (y - x).
Proof.
  ua.
  generalize (pilot_model_accel_above P B M) as pilot_model_accel_above_traj. intro.
  rewrite Bdef in pilot_model_accel_above_traj. simpl in pilot_model_accel_above_traj.
  intros x xinterval vmaxltvx y yinterval [zltymx ymxlttt].
  
  generalize (Rtotal_order vmax (v y)) as vyvminto. intros.
  assert (vmax < v y \/ vmax >= v y) as vyvminrel.
  inversion_clear vyvminto as [vyltvmin | [vyeqvmin | vygtvmin]].
  left. assumption. right. right. assumption. right. left. assumption.
  clear vyvminto.
  inversion_clear vyvminrel as [vyltvmin | vygevmin ].
  apply pilot_model_accel_above_traj. assumption. fourier. assumption. fourier. assumption.
  apply Rge_le in vygevmin.

  set (f := (fun q => v q - vmax)).
  assert (continuity f) as contf. unfold f. assume contv.
  reg.
  assert (0 < f x ) as fxlt0. unfold f. fourier.
  assert (x < y) as xlty. fourier.
  assert (f y <= 0) as fyge0. unfold f. fourier.
  generalize (first_leg_drop f x y contf xlty fxlt0 fyge0) as flr.
  intros. inversion_clear flr as [p [[xltp pley] [fpeq0 rst]]].
  unfold f in *.

  assume aalt0. rename aalt1 into aalt00. (* rename H0 into aalt00. *)
  apply (Rle_trans _ (vmax - v x) _).
  Radd (v x). setr vmax. setl (v y).
  assumption.
  left. apply (Rmult_lt_reg_l (/(-aa))).
  apply Rinv_0_lt_compat. setl (- 0).
  apply Ropp_lt_cancel. repeat rewrite Ropp_involutive.
  fourier.
  setr (- (y - x)).
  intro. rewrite H in aalt00. apply (Rlt_irrefl 0). assumption.
  setl (-((vmax - v x) / aa)).
  intro. rewrite H in aalt00. apply (Rlt_irrefl 0). assumption.
  apply Ropp_lt_cancel. repeat rewrite Ropp_involutive.
  assumption.
Qed.

Lemma pilot_model_accel_at_upper_limit :
  forall {t1 t2 z v a} (P: Path z v a) B (M: Maneuver t1 t2 P B)
         x, t1 <= x < t2 -> vmax B < v x  ->
            forall y, t1 <= y < t2 -> 0 < y - x /\ y - x = (vmax B - v x) / (aa B) ->
                                v y - v x <= (aa B) * (y - x).
Proof.
  ua.
  generalize (pilot_model_accel_above_limit P B M) as pilot_model_accel_above_limit_traj. intro.
  rewrite Bdef in pilot_model_accel_above_limit_traj. simpl in pilot_model_accel_above_limit_traj.
  intros x xinterval vmaxltvx y yinterval [zltymx ymeqvm].
  inversion xinterval as [t1ley yltt2].
  inversion yinterval as [t1lex xltt2].

  Radd (v x).
  setl (v y).
  set (fll := (fct_cte aa * (id - fct_cte x) + fct_cte (v x))%F).
  assert (continuity fll) as contfll. unfold fll. reg.
  change ( v y <= fll y).
  assume contv.
  apply limpoint; try assumption. (* clear H1. *)
  exists x. split.
  fourier.
  intros x0 xltx0lty.
  unfold fll, fct_cte, mult_fct, id, minus_fct, plus_fct.
  Radd (- v x). setr (aa * (x0 - x)). setl (v x0 - v x).
  inversion_clear xltx0lty.
  apply pilot_model_accel_above_limit_traj; try assumption.
  split; fourier. split. 
  Radd x. setl x. setr x0. assumption.
  rewrite <- ymeqvm.
  Radd x. setl x0. setr y.
  assumption.
Qed.

Lemma pilot_model_accel_downto_limit :
  forall {t1 t2 z v a} (P: Path z v a) B (M: Maneuver t1 t2 P B)
         x, t1 <= x < t2 -> vmax B < v x ->
            forall y, t1 <= y < t2 -> 0 < y - x <= (vmax B - v x) / (aa B) ->
                      v y - v x <= (aa B) * (y - x).
Proof.
  ua.
  generalize (pilot_model_accel_above_limit P B M) as pilot_model_accel_above_limit_traj. intro.
  rewrite Bdef in pilot_model_accel_above_limit_traj. simpl in pilot_model_accel_above_limit_traj.
  generalize (pilot_model_accel_at_upper_limit P B M) as pilot_model_accel_at_upper_limit_traj. intro.
  rewrite Bdef in pilot_model_accel_at_upper_limit_traj. simpl in pilot_model_accel_at_upper_limit_traj.
  intros x xinterval vxltvmin y yinterval [zltymx [ymxltvm | ymxeqvm]].
  inversion xinterval as [t1ley yltt2].
  inversion yinterval as [t1lex xltt2].

  apply pilot_model_accel_above_limit_traj; try assumption.
  split; try assumption.
  apply pilot_model_accel_at_upper_limit_traj; try assumption.
  split. assumption. assumption.
Qed.


Lemma above_vmin_lower_left_limiting_trajectory :
  forall {t1 t2 z v a} (P: Path z v a) B (M: Maneuver t1 t2 P B)
         t (tinterval : t1 <= t < t2) (zlet1 : 0 <= t1) (r : vmin B <= v t1)
         (s : (t-t1) <= (vmin B - v t1) / (amin B)),
    (amin B) / 2 * ((t-t1) * (t-t1)) + (v t1) * (t-t1) + (z t1) <= z t.
Proof.
  ua.
  generalize (pilot_model_maintains_lower_bound P B M) as pilot_model_maintains_lower_bound_traj. intro.
  rewrite Bdef in pilot_model_maintains_lower_bound_traj. simpl in pilot_model_maintains_lower_bound_traj.
  intros.
  inversion tinterval as [t1let tltt2].

  generalize contv as contv0; intro.
  rewrite <- dpeqv in contv0.
  generalize conta as conta0; intro.
  rewrite <- dveqa in conta0.

  set (pfun := (mkC1 contv0)).
  generalize (RiemannInt_P32 pfun t1 t) as vintegr. intros.
  generalize (FTC_Riemann pfun vintegr) as vintval. intros.
  simpl in vintegr, vintval.
    apply (Rplus_le_reg_l (- (z t1)));
    setr (z t - z t1);
    rewrite <- vintval;
    try setl (amin / 2 * ((t-t1) * (t-t1)) + (v t1) * (t-t1)).
  set (f := (fct_cte (amin/2) * comp Rsqr (id - fct_cte t1)+ fct_cte (v t1) * (id - fct_cte t1))%F);
    establish_deriv2 f' (fct_cte amin * (id - fct_cte t1) + fct_cte (v t1))%F f;
  rename H into fpf;
  assert (continuity (derive f fpf)) as contf;
    [rewrite fe; unfold f'; reg | idtac];
  set (ffun := (mkC1 contf));
  generalize (RiemannInt_P32 ffun t1 t) as fintegr; intros;
  generalize (FTC_Riemann ffun fintegr) as fintval; intros;
  simpl in fintval;
  change ( f t <= RiemannInt vintegr);
  assert (f t = f t - f t1) as fzero;
  [unfold f, fct_cte, plus_fct, mult_fct, Rsqr, id, comp, minus_fct;
    field | rewrite fzero; clear fzero;
  simpl in fintegr, fintval;
  rewrite <- fintval].
  apply RiemannInt_P19 ; [assumption | idtac].
  intros x t1ltxltt.
  rewrite fe, dpeqv;
  unfold f', fct_cte, mult_fct, plus_fct, id, minus_fct;
  apply (Rplus_le_reg_r (- v t1));
  setl (amin * (x-t1));
  setr (v x - v t1).
  set (vfun := (mkC1 conta0));
  generalize (RiemannInt_P32 vfun t1 x) as aintegr; intros;
  generalize (FTC_Riemann vfun aintegr) as aintval; intros;
  simpl in aintval, aintegr; clear vfun;
  rewrite <- aintval.
  set (g := (fct_cte amin * (id - fct_cte t1))%F);
    establish_deriv2 g' (fct_cte amin)%F g;
  rename H into gpf;
  assert (continuity (derive g gpf)) as contg;
    [rewrite fe0; unfold g'; reg | idtac];
  set (gfun := (mkC1 contg));
  generalize (RiemannInt_P32 gfun t1 x) as gintegr; intros;
  generalize (FTC_Riemann gfun gintegr) as gintval; intros;
  change (g x <= RiemannInt aintegr).
  assert (g x = g x - g t1); [unfold g;
  unfold fct_cte, mult_fct, id, minus_fct; setr (amin * (x-t1)); reflexivity | rewrite H ];
  simpl in gintval;
  rewrite <- gintval;
  apply RiemannInt_P19;
  [inversion t1ltxltt as [t1ltx xltt]; left; assumption | intros; rewrite fe0, dveqa];
  unfold g', fct_cte.
  clear H gintval gintegr gfun contg fe0 gpf g' g aintegr aintval.
  clear fintval fintegr ffun contf fe fpf f' f vintegr vintval.

  clear pfun.
  rewrite dpeqv in contv0.
  inversion_clear H0 as [zltx0 x0ltx].
  inversion t1ltxltt.
  assert (t1 <= t1 < t2) as t1interval. split; fourier.
  assert (t1 <= x0 < t2) as x0interval. split; fourier.
    generalize (pilot_model_maintains_lower_bound_traj t1 t1interval r x0 x0interval zltx0) as vminbnd. intros.

  inversion_clear vminbnd as [vminltvx0 | vmineqvx0].
  generalize (Rtotal_order (v x0) vmax) as vmaxorder; intros;
  inversion_clear vmaxorder as [vltvmax | [veqvmax | vgtvmax]].
  assert (vmin < v x0 < vmax) as vx0pos. split. assumption. assumption.

  generalize (vwithin _ x0interval vx0pos) as ax0pos. intros.
  inversion_clear ax0pos as [aminleax0 ax0leamax]. assumption.

  generalize (vatupper _ x0interval veqvmax) as ax0pos. intros.
  inversion_clear ax0pos as [aminleax0 ax0leamax]. assumption.

  generalize (vabove _ x0interval vgtvmax) as ax0pos. intros.
  inversion_clear ax0pos as [aminleax0 ax0leamax]. assumption.

  symmetry in vmineqvx0.
  generalize (vatlower _ x0interval vmineqvx0) as ax0pos. intros.
  inversion_clear ax0pos as [aminleax0 ax0leamax].
  assume aminleaa. assume aalt0. fourier.
Qed.



Lemma below_vmin_lower_left_limiting_trajectory_upto :
  forall {t1 t2 z v a} (P: Path z v a) B (M: Maneuver t1 t2 P B)
         t (tinterval : t1 <= t < t2) (zlet1 : 0 <= t1) (r : v t1 < vmin B)
         (s : (t-t1) < (vmin B - v t1) / (ab B)),
    (ab B) / 2 * ((t-t1) * (t-t1)) + v t1 * (t-t1) + z t1 <= z t.
Proof.
  ua.
  generalize (pilot_model_accel_upto_limit P B M) as pilot_model_accel_upto_limit_traj. intro.
  rewrite Bdef in pilot_model_accel_upto_limit_traj. simpl in pilot_model_accel_upto_limit_traj.
  intros.
  inversion tinterval as [t1let tltt2].

  generalize contv as contv0; intro.
  rewrite <- dpeqv in contv0.
  generalize conta as conta0; intro.
  rewrite <- dveqa in conta0.

  set (pfun := (mkC1 contv0)).
  generalize (RiemannInt_P32 pfun t1 t) as vintegr. intros.
  generalize (FTC_Riemann pfun vintegr) as vintval. intros.
  simpl in vintegr, vintval.


    apply (Rplus_le_reg_l (- (z t1)));
    setr (z t - z t1);
    rewrite <- vintval;
    try setl (ab / 2 * ((t-t1) * (t-t1)) + v t1 * (t-t1)).
    set (f := (fct_cte (ab/2) * comp Rsqr (id - fct_cte t1)+ fct_cte (v t1) * (id - fct_cte t1))%F);
    establish_deriv2 f' (fct_cte ab * (id - fct_cte t1) + fct_cte (v t1))%F f;
  rename H into fpf;
  assert (continuity (derive f fpf)) as contf;
    [rewrite fe; unfold f'; reg | idtac];
  set (ffun := (mkC1 contf));
  generalize (RiemannInt_P32 ffun t1 t) as fintegr; intros;
  generalize (FTC_Riemann ffun fintegr) as fintval; intros;
  change ( f t <= RiemannInt vintegr);
  assert (f t = f t - f t1) as fzero;
  [unfold f, fct_cte, plus_fct, mult_fct, minus_fct, comp, Rsqr, id;
  field | rewrite fzero; clear fzero;
  simpl in fintegr, fintval;
  rewrite <- fintval].
  apply RiemannInt_P19. assumption.
  intros x tgtxgtt1;
  assert (t1 <= x <= t) as xge0let;
    [ inversion tgtxgtt1; split; left; assumption | idtac].
  rewrite fe, dpeqv.
  unfold f', fct_cte, mult_fct, plus_fct, id, minus_fct.

  clear pfun.
  rewrite dpeqv in contv0.
(*  inversion_clear H0 as [zltx0 x0ltx]. *)
  assert (0 < x - t1 <= (vmin - v t1) / ab) as x0pos.
  split. Radd t1. setl t1. setr x. inversion_clear tgtxgtt1 as [zltx xltt]. assumption.
  left. Radd t1. setl x. inversion_clear tgtxgtt1 as [zltx xltt].
  apply (Rlt_trans _ t _). assumption. Radd (-t1). setl (t - t1). setr ((vmin - v t1)/ab).
  intro. clear Bdef. rewrite H in zltab.
  apply (Rlt_irrefl 0). assumption.
  assumption.

  assert (t1 <= t1 < t2) as t1interval. split; fourier.
  assert (t1 <= x < t2) as xinterval.
  inversion tgtxgtt1.
  split; fourier.
  generalize (pilot_model_accel_upto_limit_traj t1 t1interval r x xinterval x0pos) as vminbnd. intros.

  apply (Rplus_le_reg_r (- v t1)).
  setl (ab * (x - t1)).
  setr (v x - v t1). assumption.
Qed.

Lemma below_vmin_lower_left_limiting_trajectory :
    forall {t1 t2 z v a} (P: Path z v a) B (M: Maneuver t1 t2 P B)
           t (tinterval : t1 <= t < t2) (zlet1 : 0 <= t1) (r : v t1 < vmin B)
           (s : t-t1 <= (vmin B - v t1) / (ab B)),
      (ab B) / 2 * ((t-t1) * (t-t1)) + v t1 * (t-t1) + z t1 <= z t.
Proof.
  ua.
  generalize (below_vmin_lower_left_limiting_trajectory_upto P B M) as
      below_vmin_lower_left_limiting_trajectory_upto_traj. intro.
  rewrite Bdef in below_vmin_lower_left_limiting_trajectory_upto_traj.
  simpl in below_vmin_lower_left_limiting_trajectory_upto_traj.
  intros.
  inversion tinterval as [t1let tltt2].

  rename s into sold.
  inversion_clear sold as [s | s].
  apply below_vmin_lower_left_limiting_trajectory_upto_traj; try assumption.
  assert (0<=(t-t1)) as tmt1ge0. fourier.
  inversion_clear tmt1ge0 as [tmt1gt0 | tmt1eq0].
  set (fll := (fct_cte (ab/2) * comp Rsqr (id - fct_cte t1) +
               fct_cte (v t1) * (id-fct_cte t1) + fct_cte (z t1))%F).
  assert (continuity fll). unfold fll. reg.
  change (fll t <= z t).
  assume contz.
  apply limpoint; try assumption. (* clear H0. *)
  exists t1. split. fourier. 
  intros.
  inversion_clear H0 as [t1ltx xltt].
  apply below_vmin_lower_left_limiting_trajectory_upto_traj; try assumption.
  split. left. assumption. fourier. rewrite <- s. Radd t1. setl x. setr t. assumption.
  apply False_ind.
  rewrite s in tmt1eq0.
  assert (v t1 = vmin). Radd (- v t1).
  setl 0. setr (vmin - v t1).
  
  assume zltab. (* rename H into zltab0. *)
  apply (Rmult_eq_reg_l (/ ab )).
  setl 0.
  intro. rewrite H in zltab0. apply (Rlt_irrefl 0). assumption.
  setr ((vmin - v t1) / ab).
  intro. rewrite H in zltab0. apply (Rlt_irrefl 0). assumption.
  assumption.
  apply Rinv_neq_0_compat. discrR.
  intro. rewrite H in zltab0. apply (Rlt_irrefl 0). assumption.
  rewrite H in r.
  apply (Rlt_irrefl vmin). assumption.
Qed.


Lemma above_vmin_lower_right_limiting_trajectory :
  forall {t1 t2 z v a} (P: Path z v a) B (M: Maneuver t1 t2 P B)
         t (tinterval : t1 <= t < t2) (zlet1 : 0 <= t1) (r : vmin B <= v t1)
         (s : (vmin B - v t1) / (amin B) <= t-t1),
    (vmin B) * (t-t1) - ((vmin B - v t1)/(amin B)) * (vmin B - v t1)/2 + z t1 <= z t.
Proof.
  ua.
  generalize (above_vmin_lower_left_limiting_trajectory P B M) as
      above_vmin_lower_left_limiting_trajectory_traj. intro.
  rewrite Bdef in above_vmin_lower_left_limiting_trajectory_traj.
  simpl in above_vmin_lower_left_limiting_trajectory_traj.

  generalize (pilot_model_maintains_lower_bound P B M) as pilot_model_maintains_lower_bound_traj. intro.
  rewrite Bdef in pilot_model_maintains_lower_bound_traj.
  simpl in pilot_model_maintains_lower_bound_traj.
  intros.
  inversion tinterval as [t1let tltt2].

  assume aminleaa. assume aalt0.
  rename aalt1 into aalt00. (*rename H into aminleaa0. rename H0 into aalt00.*)
  assert ((vmin*vmin - (v t1)*(v t1))/(2*amin) + z t1 <= z ((vmin - v t1)/amin + t1)).
  assert (0 <= (vmin - v t1) / amin). inversion_clear r.
  setr ((v t1 - vmin) / (- amin)).
  intro. subst. assert (0 < 0). fourier. apply (Rlt_irrefl 0). assumption.
  setr ((v t1 - vmin) * (/ -amin)).
  intro. subst. assert (0 < 0). fourier. apply (Rlt_irrefl 0). assumption.
  assert (0 = 0*0). field. rewrite H0 at 1.
  left. apply Rmult_ge_0_gt_0_lt_compat. right. reflexivity. fourier. fourier. 
  apply Rinv_0_lt_compat. fourier.
  rewrite H. setr 0.
  intro. subst. assert (0 < 0). fourier. apply (Rlt_irrefl 0). assumption. right. reflexivity.
  assert ((vmin - v t1) / amin + t1 - t1 <= (vmin - v t1) / amin). right. setl ((vmin - v t1) / amin).
  intro. subst. assert (0 < 0). fourier. apply (Rlt_irrefl 0). assumption.
  reflexivity.
  assert (t1 <= (vmin - v t1) / amin + t1 < t2) as vmininterval.
  split. Radd (-t1). setl 0. setr ((vmin - v t1) / amin).
  intro. subst. assert (0 < 0). fourier. apply (Rlt_irrefl 0). assumption. assumption.
  assert ((vmin - v t1) / amin + t1 <= t). Radd (-t1). setl ((vmin - v t1) / amin).
  intro. subst. assert (0 < 0). fourier. apply (Rlt_irrefl 0). assumption. assumption.
  set (tmp := (vmin - v t1) / amin) in *. fourier.
  
  generalize (above_vmin_lower_left_limiting_trajectory_traj ((vmin - v t1) / amin + t1) vmininterval
             zlet1 r H0). intros.
  setl (amin / 2 * ((vmin - v t1) / amin * ((vmin - v t1) / amin)) +
        v t1 * ((vmin - v t1) / amin) + z t1).
  intro. subst. assert (0 < 0). fourier. apply (Rlt_irrefl 0). assumption.
  setl (amin / 2 *
       (((vmin - v t1) / amin + t1 - t1) *
        ((vmin - v t1) / amin + t1 - t1)) +
       v t1 * ((vmin - v t1) / amin + t1 - t1) + z t1).
  intro. subst. assert (0 < 0). fourier. apply (Rlt_irrefl 0). assumption.
  assumption.

  setl (vmin * ( (t-t1) - ((vmin - v t1)/amin)) +
        (vmin * vmin - v t1 * v t1) / (2*amin) + z t1).
  intro. subst. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption.
  set (tt := (vmin - v t1) / amin + t1).
  change ((vmin * vmin - v t1 * v t1) / (2 * amin) + z t1 <= z tt) in H.
  assert (tt <= t) as s1.
  unfold tt. Radd (-t1). setr (t-t1). setl ((vmin - v t1) / amin).
  intro. rewrite H0 in *.
  assert (aa >= 0). fourier.
  apply (Rge_not_lt aa 0 H1 aalt00).
  assumption.
  apply (Rle_trans _ (vmin * (t - tt) + z tt) _).
  Radd (- vmin * (t - tt)). setr (z tt). unfold tt.
  setl ((vmin * vmin - v t1 * v t1) / (2 * amin) + z t1).
  intro. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption.
  assumption.

  generalize contv as contv0; intro.
  rewrite <- dpeqv in contv0.
  generalize conta as conta0; intro.
  rewrite <- dveqa in conta0.

  set (pfun := (mkC1 contv0)).
  generalize (RiemannInt_P32 pfun tt t) as vintegr. intros.
  generalize (FTC_Riemann pfun vintegr) as vintval. intros.
  simpl in vintegr, vintval.
  apply (Rplus_le_reg_l (- (z tt)));
    setl (vmin * (t - tt));
    setr (z t - z tt).
  rewrite <- vintval.
  set (f := (fct_cte vmin * id)%F).
    establish_deriv2 f' (fct_cte vmin)%F f.
  rename H0 into fpf.
  assert (continuity (derive f fpf)) as contf;
    [rewrite fe; unfold f'; reg | idtac].
  set (ffun := (mkC1 contf)).
  generalize (RiemannInt_P32 ffun tt t) as fintegr; intros;
  generalize (FTC_Riemann ffun fintegr) as fintval; intros.
  setl (vmin * t - vmin * tt).
  change ( f t - f tt <= RiemannInt vintegr).
  simpl in fintegr, fintval.
  rewrite <- fintval.
  apply RiemannInt_P19. assumption.
  intros x ttltxltt.
  assert (tt <= x <= t) as ttlexlet.
  inversion ttltxltt. split; left; assumption.
  rewrite fe, dpeqv.
  unfold f', fct_cte, mult_fct, plus_fct, id.
  assert (t1 <= t1 < t2) as t1interval. split. right. reflexivity. inversion tinterval.
  inversion H0. fourier. rewrite <- H2 in H1. assumption.
  eapply pilot_model_maintains_lower_bound_traj. apply t1interval. apply r.
  inversion ttltxltt as [ttltx xltt]. split.
  assert (t1 <= tt) as t1gett.
  unfold tt. Radd (-t1). setl 0. setr ((v t1 - vmin) * (/ -amin)).
  intro. assert (0 < 0). fourier. apply (Rlt_irrefl 0). assumption.
  inversion_clear r. setl (0*0). left.
  apply Rmult_ge_0_gt_0_lt_compat. right. reflexivity. fourier. fourier. 
  apply Rinv_0_lt_compat. fourier.
  rewrite H0. setr 0.
  intro. assert (0 < 0). fourier. apply (Rlt_irrefl 0). assumption.
  right. reflexivity.

  fourier. fourier.
  assert (t1 <= tt) as zlett. unfold tt.
  setr (  ((v t1 - vmin) * / - amin) + t1).
  intro. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption.
  Radd (-t1). setl 0. setr ((v t1 - vmin) * / - amin).
  intro. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption.
  inversion_clear r.

  left.
  assert (0 = 0*0). field. rewrite H1 at 1.
  apply Rmult_ge_0_gt_0_lt_compat. right. reflexivity. fourier. fourier.
  apply Rinv_0_lt_compat. fourier.
  rewrite H0. setr 0.
  intro. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption.
  right. reflexivity. inversion_clear ttltxltt. fourier.
Qed.


Lemma below_vmin_lower_right_limiting_trajectory :
  forall {t1 t2 z v a} (P: Path z v a) B (M: Maneuver t1 t2 P B)
         t (tinterval : t1 <= t < t2) (zlet1 : 0 <= t1) (r : v t1 < vmin B)
         (s : (vmin B - v t1) / (ab B) <= t-t1),
    (vmin B)* (t-t1) - ((vmin B - v t1)/(ab B)) * (vmin B - v t1)/2 + z t1 <= z t.
Proof.
  ua.
  generalize (below_vmin_lower_left_limiting_trajectory P B M) as
      below_vmin_lower_left_limiting_trajectory_traj. intro.
  rewrite Bdef in below_vmin_lower_left_limiting_trajectory_traj.
  simpl in below_vmin_lower_left_limiting_trajectory_traj.

  generalize (pilot_model_accel_upto_limit P B M) as
      pilot_model_accel_upto_limit_traj. intro.
  rewrite Bdef in pilot_model_accel_upto_limit_traj.
  simpl in pilot_model_accel_upto_limit_traj.

  generalize (pilot_model_maintains_lower_bound P B M) as
      pilot_model_maintains_lower_bound_traj. intro.
  rewrite Bdef in pilot_model_maintains_lower_bound_traj.
  simpl in pilot_model_maintains_lower_bound_traj.

  intros.

  assume zltab. (* rename H into zltab0. *)
  assert ((vmin*vmin - (v t1)*(v t1))/(2*ab) + z t1 <= z ((vmin - v t1)/ab + t1)).
  assert (0 <= (vmin - v t1) / ab).
  setr ((vmin - v t1) * / ab).
  intro. assume zltab. 
  subst. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption.
  assert (0 = 0*0). field. rewrite H at 1. left.
  apply Rmult_ge_0_gt_0_lt_compat. right. reflexivity. fourier. fourier.
  apply Rinv_0_lt_compat. apply zltab.
  assert ((vmin - v t1) / ab + t1 - t1 <= (vmin - v t1) / ab). right. setl ((vmin - v t1) / ab).
  intro. subst. assert (0 < 0). fourier. apply (Rlt_irrefl 0). assumption.
  reflexivity.
  assert (t1 <= (vmin - v t1) / ab + t1 < t2) as vmininterval.
  split. Radd (-t1). setl 0. setr ((vmin - v t1) / ab).
  intro. subst. assert (0 < 0). fourier. apply (Rlt_irrefl 0). assumption. assumption.
  assert ((vmin - v t1) / ab + t1 <= t). Radd (-t1). setl ((vmin - v t1) / ab).
  intro. subst. assert (0 < 0). fourier. apply (Rlt_irrefl 0). assumption. assumption.
  set (tmp := (vmin - v t1) / ab) in *. inversion tinterval. fourier.

  generalize (below_vmin_lower_left_limiting_trajectory_traj
                ((vmin - v t1)/ab+t1) vmininterval zlet1 r H0). intros.
  setl (ab / 2 *
       (((vmin - v t1) / ab + t1 - t1) * ((vmin - v t1) / ab + t1 - t1)) +
       v t1 * ((vmin - v t1) / ab + t1 - t1) + z t1).
  intro. subst. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption. assumption.

  setl (vmin * ( (t-t1) - ((vmin - v t1)/ab)) +
        (vmin * vmin - v t1 * v t1) / (2*ab) + z t1).
  intro. subst. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption.
  set (tt := (vmin - v t1) / ab + t1).
  change ((vmin * vmin - v t1 * v t1) / (2 * ab) + z t1 <=
          z tt) in H.
  assert (tt <= t) as s1.
  unfold tt. Radd (-t1). setr (t-t1). setl ((vmin - v t1) / ab).
  intro. rewrite H0 in *.  apply (Rlt_irrefl 0). assumption.
  assumption.
  
  apply (Rle_trans _ (vmin * (t - tt) + z tt) _).
  Radd (- vmin * (t - tt)). setr (z tt). unfold tt.
  setl ((vmin * vmin - v t1 * v t1) / (2 * ab) + z t1).
  intro. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption.
  assumption.

  generalize contv as contv0; intro.
  rewrite <- dpeqv in contv0.
  generalize conta as conta0; intro.
  rewrite <- dveqa in conta0.

  set (pfun := (mkC1 contv0)).
  generalize (RiemannInt_P32 pfun tt t) as vintegr. intros.
  generalize (FTC_Riemann pfun vintegr) as vintval. intros.
  simpl in vintegr, vintval.
  apply (Rplus_le_reg_l (- (z tt)));
    setl (vmin * (t - tt));
    setr (z t - z tt).
  rewrite <- vintval.
  set (f := (fct_cte vmin * id)%F).
    establish_deriv2 f' (fct_cte vmin)%F f.
  rename H0 into fpf.
  assert (continuity (derive f fpf)) as contf;
    [rewrite fe; unfold f'; reg | idtac].
  set (ffun := (mkC1 contf)).
  generalize (RiemannInt_P32 ffun tt t) as fintegr; intros;
  generalize (FTC_Riemann ffun fintegr) as fintval; intros.
  setl (vmin * t - vmin * tt).
  change ( f t - f tt <= RiemannInt vintegr).
  simpl in fintegr, fintval.
  rewrite <- fintval.
  apply RiemannInt_P19. assumption.
  intros x ttltxltt.
  assert (tt <= x <= t) as ttlexlet.
  inversion ttltxltt. split; left; assumption.
  rewrite fe, dpeqv.
  unfold f', fct_cte, mult_fct, plus_fct, id.
  assert (0 < tt - t1 <= (vmin - v t1) / ab) as ttpos.
  split.
  unfold tt.
  setr ((vmin - v t1) * / ab).
  intro. rewrite H0 in zltab0. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption.
  assert (0 = 0*0). field. rewrite H0 at 1. 
  apply Rmult_ge_0_gt_0_lt_compat. right. reflexivity. fourier. fourier.
  apply Rinv_0_lt_compat. fourier.
  Radd t1.
  setl tt. unfold tt. right. reflexivity.
  assert (ab * (tt - t1) + v t1 <= v tt) as vttval.
  Radd (- v t1). setl (ab * (tt - t1)). setr (v tt - v t1).
  assert (t1 <= t1 < t2) as t1interval. inversion tinterval. split; fourier.
  assert (t1 <= tt < t2) as ttinterval. split.
  inversion ttpos. left. fourier. inversion ttltxltt. inversion tinterval. fourier.
  apply (pilot_model_accel_upto_limit_traj t1 t1interval r tt ttinterval ttpos).
  unfold tt in vttval at 1.
  assert (ab * ((vmin - v t1) / ab + t1 - t1) + v t1 = vmin).
  field.
  intro. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption.
  rewrite H0 in vttval.
  eapply pilot_model_maintains_lower_bound_traj.
  assert (t1 <= tt < t2) as ttinterval. split.
  inversion ttpos. left. fourier. inversion ttltxltt. inversion tinterval. fourier.
  eapply ttinterval.
  apply vttval.
  inversion_clear ttltxltt. split.
  inversion ttpos. fourier.
  inversion ttlexlet. inversion tinterval. fourier.
  inversion ttltxltt.
  assumption.
Qed.

Lemma bounded_below :
  forall {t1 t2 z v a} (P: Path z v a) B (M: Maneuver t1 t2 P B)
         t (tinterval : t1 <= t < t2) (zlet1 : 0 <= t1),
    K (amin B) (ab B) (v t1) (vmin B) (z t1) (t-t1) <= z t (*<= K aa amax (v 0) vmax (z 0) t *).
Proof.
  ua.
  generalize (above_vmin_lower_left_limiting_trajectory P B M) as 
    above_vmin_lower_left_limiting_trajectory_traj. intro.
  rewrite Bdef in above_vmin_lower_left_limiting_trajectory_traj.
  simpl in above_vmin_lower_left_limiting_trajectory_traj.
  generalize (above_vmin_lower_right_limiting_trajectory P B M) as 
    above_vmin_lower_right_limiting_trajectory_traj. intro.
  rewrite Bdef in above_vmin_lower_right_limiting_trajectory_traj.
  simpl in above_vmin_lower_right_limiting_trajectory_traj.
  generalize (below_vmin_lower_left_limiting_trajectory P B M) as 
    below_vmin_lower_left_limiting_trajectory_traj. intro.
  rewrite Bdef in below_vmin_lower_left_limiting_trajectory_traj.
  simpl in below_vmin_lower_left_limiting_trajectory_traj.
  generalize (below_vmin_lower_right_limiting_trajectory P B M) as 
    below_vmin_lower_right_limiting_trajectory_traj. intro.
  rewrite Bdef in below_vmin_lower_right_limiting_trajectory_traj.
  simpl in below_vmin_lower_right_limiting_trajectory_traj.

  
  intros.
  assume aalt0. rename aalt1 into aalt00.
  assume aminleaa. (* rename H into aminleaa0. *)
  assume zltab. (* rename H into zltab0. *)

  unfold K.
  destruct (total_order_T vmin (v t1)); [
      assert (vmin <= v t1) as r; [inversion s ;
                                   [ left; assumption | right ; assumption] |
                                  idtac]; clear s |
      idtac]; [
  destruct (total_order_T (t-t1) ((vmin - v t1) / amin)); [
      assert ((t-t1) <= (vmin - v t1) / amin) as s0; [inversion s ;
                                   [ left; assumption | right ; assumption] |
                                  idtac]; clear s |
      idtac] |
  destruct (total_order_T (t-t1) ((vmin - v t1) / ab)); [
      assert ((t-t1) <= (vmin - v t1) / ab) as s0; [inversion s ;
                                   [ left; assumption | right ; assumption] |
                                  idtac]; clear s |
      idtac]];
    unfold J;
    simpl.

  setl (amin / 2 * ((t-t1) * (t-t1)) + v t1 * (t-t1) + z t1).
  apply above_vmin_lower_left_limiting_trajectory_traj; try assumption.
  setl (vmin * (t-t1) - (vmin - v t1) / amin * (vmin - v t1) / 2 + z t1).
  intro. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption.
  apply above_vmin_lower_right_limiting_trajectory_traj; try assumption.
  left. assumption.
  setl (ab / 2 * ((t-t1) * (t-t1)) + v t1 * (t-t1) + z t1).
  apply below_vmin_lower_left_limiting_trajectory_traj; try assumption.
  setl (vmin * (t-t1) - (vmin - v t1) / ab * (vmin - v t1) / 2 + z t1).
  intro. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption.
  apply below_vmin_lower_right_limiting_trajectory_traj; try assumption.
  left. assumption.
Qed.

Lemma below_vmax_upper_left_limiting_trajectory :
  forall {t1 t2 z v a} (P: Path z v a) B (M: Maneuver t1 t2 P B)
         t (tinterval : t1 <= t < t2) (zlet1 : 0 <= t1)
         (r : v t1 <= vmax B) (s : t-t1 <= (vmax B - v t1) / (amax B)),
    z t <= (amax B) / 2 * ((t-t1) * (t-t1)) + v t1 * (t-t1) + z t1.
Proof.
  ua.
  generalize (pilot_model_maintains_upper_bound P B M) as pilot_model_maintains_upper_bound_traj.  intro.
  rewrite Bdef in pilot_model_maintains_upper_bound_traj.
  simpl in pilot_model_maintains_upper_bound_traj.
  
  intros.

  generalize contv as contv0; intro.
  rewrite <- dpeqv in contv0.
  generalize conta as conta0; intro.
  rewrite <- dveqa in conta0.

  set (pfun := (mkC1 contv0)).
  generalize (RiemannInt_P32 pfun t1 t) as vintegr. intros.
  generalize (FTC_Riemann pfun vintegr) as vintval. intros.
  simpl in vintegr, vintval.
    apply (Rplus_le_reg_l (- (z t1)));
    setl (z t - z t1);
    rewrite <- vintval;
    try setr (amax / 2 * ((t-t1) * (t-t1)) + v t1 * (t-t1)).
  set (f := (fct_cte (amax/2) * comp Rsqr (id - fct_cte t1) + fct_cte (v t1) * (id - fct_cte t1))%F);
    establish_deriv2 f' (fct_cte amax * (id - fct_cte t1) + fct_cte (v t1))%F f;
  rename H into fpf;
  assert (continuity (derive f fpf)) as contf;
    [rewrite fe; unfold f'; reg | idtac];
  set (ffun := (mkC1 contf));
  generalize (RiemannInt_P32 ffun t1 t) as fintegr; intros;
  generalize (FTC_Riemann ffun fintegr) as fintval; intros;
  change ( RiemannInt vintegr <= f t );
  assert (f t = f t - f t1) as fzero;
  [unfold f, fct_cte, plus_fct, mult_fct, Rsqr, id, minus_fct, comp;
  field | rewrite fzero; clear fzero;
  simpl in fintegr, fintval;
  rewrite <- fintval];
  apply RiemannInt_P19 ; [inversion tinterval; assumption | idtac];
  intros x tgtxgt0;
  assert (t1 <= x <= t) as xge0let;
    [ inversion tgtxgt0; split; left; assumption | idtac];
  rewrite fe, dpeqv;
  unfold f', fct_cte, mult_fct, plus_fct, id, minus_fct;
  apply (Rplus_le_reg_r (- v t1));
  setr (amax * (x-t1));
  setl (v x - v t1);
  set (vfun := (mkC1 conta0));
  generalize (RiemannInt_P32 vfun t1 x) as aintegr; intros;
  generalize (FTC_Riemann vfun aintegr) as aintval; intros;
  simpl in aintval, aintegr; clear vfun;
  rewrite <- aintval;
  set (g := (fct_cte amax * (id - fct_cte t1))%F);
    establish_deriv2 g' (fct_cte amax)%F g;
  rename H into gpf;
  assert (continuity (derive g gpf)) as contg;
    [rewrite fe0; unfold g'; reg | idtac];
  set (gfun := (mkC1 contg));
  generalize (RiemannInt_P32 gfun t1 x) as gintegr; intros;
  generalize (FTC_Riemann gfun gintegr) as gintval; intros;
  change (RiemannInt aintegr <= g x);
  assert (g x = g x - g t1); [ unfold g;
  unfold fct_cte, mult_fct, id, minus_fct; setr (amax *( x - t1)) ; reflexivity | rewrite H ];
  simpl in gintval;
  rewrite <- gintval;
  apply RiemannInt_P19;
  [left; inversion_clear tgtxgt0; assumption | intros; rewrite fe0, dveqa];
  unfold g', fct_cte;
  clear H gintval gintegr gfun contg fe0 gpf g' g aintegr aintval xge0let;
  clear fintval fintegr ffun contf fe fpf f' f vintegr vintval.

  clear pfun.
  rewrite dpeqv in contv0.
  inversion_clear H0 as [zltx0 x0ltx].
  
  assert (t1 <= t1 < t2) as t1interval. inversion tinterval. split; fourier.
  assert (t1 <= x0 < t2) as x0interval. inversion tinterval. inversion tgtxgt0; split; fourier.
  generalize (pilot_model_maintains_upper_bound_traj t1 t1interval r x0 x0interval zltx0) as vmaxbnd. intros.

  inversion_clear vmaxbnd as [vmaxltvx0 | vmaxeqvx0].
  generalize (Rtotal_order (v x0) vmin) as vminorder; intros;
  inversion_clear vminorder as [vltvmin | [veqvmin | vgtvmin]].

  generalize (vbelow _ x0interval vltvmin) as ax0pos. intros.
  inversion_clear ax0pos as [amaxleax0 ax0leamax]. assumption.

  generalize (vatlower _ x0interval veqvmin) as ax0pos. intros.
  inversion_clear ax0pos as [amaxleax0 ax0leamax]. assumption.

  
  assert (vmin < v x0 < vmax) as vx0pos. split. assumption. assumption.
  generalize (vwithin _ x0interval vx0pos) as ax0pos. intros.
  inversion_clear ax0pos as [amaxleax0 ax0leamax]. assumption.

  generalize (vatupper _ x0interval vmaxeqvx0) as ax0pos. intros.
  inversion_clear ax0pos as [amaxleax0 ax0leamax].
  assume ableamax. assume zltab. fourier.
Qed.

Lemma above_vmax_upper_left_limiting_trajectory_upto :
  forall {t1 t2 z v a} (P: Path z v a) B (M: Maneuver t1 t2 P B)
         t (tinterval : t1 <= t < t2) (zlet1 : 0 <= t1)
         (r : vmax B < v t1) (s : t-t1 < (vmax B - v t1) / (aa B)),
    z t <= (aa B) / 2 * ((t-t1) * (t-t1)) + v t1 * (t-t1) + z t1.
Proof.
  ua.
  generalize (pilot_model_accel_downto_limit P B M) as pilot_model_accel_downto_limit_traj. intro.
  rewrite Bdef in pilot_model_accel_downto_limit_traj.
  simpl in pilot_model_accel_downto_limit_traj.
  
  intros.

  generalize contv as contv0; intro.
  rewrite <- dpeqv in contv0.
  generalize conta as conta0; intro.
  rewrite <- dveqa in conta0.

  set (pfun := (mkC1 contv0)).
  generalize (RiemannInt_P32 pfun t1 t) as vintegr. intros.
  generalize (FTC_Riemann pfun vintegr) as vintval. intros.
  simpl in vintegr, vintval.


    apply (Rplus_le_reg_l (- (z t1)));
    setl (z t - z t1);
    rewrite <- vintval;
    try setr (aa / 2 * ((t-t1) * (t-t1)) + v t1 * (t-t1)).
    set (f := (fct_cte (aa/2) * comp Rsqr (id - fct_cte t1)+ fct_cte (v t1) * (id - fct_cte t1))%F);
    establish_deriv2 f' (fct_cte aa * (id - fct_cte t1) + fct_cte (v t1))%F f;
  rename H into fpf;
  assert (continuity (derive f fpf)) as contf;
    [rewrite fe; unfold f'; reg | idtac];
  set (ffun := (mkC1 contf));
  generalize (RiemannInt_P32 ffun t1 t) as fintegr; intros;
  generalize (FTC_Riemann ffun fintegr) as fintval; intros;
  change ( RiemannInt vintegr <= f t);
  assert (f t = f t - f t1) as fzero;
  [unfold f, fct_cte, plus_fct, mult_fct, Rsqr, id, comp, minus_fct;
  field | rewrite fzero; clear fzero;
  simpl in fintegr, fintval;
  rewrite <- fintval].
  apply RiemannInt_P19; [ inversion tinterval; assumption | idtac];
  intros x tgtxgt0;
  assert (t1 <= x <= t) as xge0let;
    [ inversion tgtxgt0; split; left; assumption | idtac];
  rewrite fe, dpeqv;
  unfold f', fct_cte, mult_fct, plus_fct, id, minus_fct.

  clear pfun.
  rewrite dpeqv in contv0.
  assert (0 < x - t1 <= (vmax - v t1) / aa) as x0pos.
  split. inversion_clear tgtxgt0 as [zltx xltt]. fourier.
  left. inversion_clear tgtxgt0 as [zltx xltt].
  apply (Rlt_trans _ (t-t1) _). fourier. assumption.
  assert (t1 <= t1 < t2) as t1interval. inversion tinterval. split; fourier.
  assert (t1 <= x < t2) as xinterval. inversion tinterval. inversion tgtxgt0; split; fourier.
  generalize (pilot_model_accel_downto_limit_traj t1 t1interval r x xinterval x0pos) as vmaxbnd. intros.

  fourier.
Qed.

Lemma above_vmax_upper_left_limiting_trajectory :
    forall {t1 t2 z v a} (P: Path z v a) B (M: Maneuver t1 t2 P B)
         t (tinterval : t1 <= t < t2) (zlet1 : 0 <= t1)
      (r : vmax B < v t1) (s : t-t1 <= (vmax B - v t1) / (aa B)),
     z t <= (aa B) / 2 * ((t-t1) * (t-t1)) + v t1 * (t-t1) + z t1.
Proof.
  ua.
  generalize (above_vmax_upper_left_limiting_trajectory_upto P B M) as
    above_vmax_upper_left_limiting_trajectory_upto_traj. intro.
  rewrite Bdef in above_vmax_upper_left_limiting_trajectory_upto_traj.
  simpl in above_vmax_upper_left_limiting_trajectory_upto_traj.
  
  intros.
  rename s into sold.
  inversion tinterval as [t1let tltt2].
  inversion_clear sold as [s | s].
  apply above_vmax_upper_left_limiting_trajectory_upto_traj; try assumption.
  set (fll := (fct_cte (aa/2) * comp Rsqr (id - fct_cte t1) + fct_cte (v t1) * (id - fct_cte t1) + fct_cte (z t1))%F).
  assert (continuity fll). unfold fll. reg.
  change (z t <= fll t).
  assume contz.
  inversion t1let. 
  apply limpoint; try assumption. (* clear H0.*)
  exists t1. split. assumption.
  intros x xinterval.
  inversion xinterval as [t1ltx xltt].

  apply above_vmax_upper_left_limiting_trajectory_upto_traj; try assumption.
  split; fourier.
  Radd t1. setl x.
  assert (t = (vmax - v t1) / aa + t1) as tdef.
  Radd (-t1). setl (t - t1). setr ((vmax - v t1) / aa).
  intro. assert (0 < 0). fourier. apply (Rlt_irrefl 0). assumption. assumption.
  rewrite <- tdef. assumption.

  apply False_ind.
  assert (0 = t - t1) as tmt1eq0. Radd t1. setl t1. setr t. assumption.
  rewrite s in tmt1eq0.
  assert (v t1 = vmax). Radd (- v t1).
  setl 0. setr (vmax - v t1).
  
  assume aalt0. rename aalt1 into aalt00.
  apply (Rmult_eq_reg_l (/ aa )).
  setl 0.
  intro. rewrite H1 in aalt00. apply (Rlt_irrefl 0). assumption.
  setr ((vmax - v t1) / aa).
  intro. rewrite H1 in aalt00. apply (Rlt_irrefl 0). assumption.
  assumption.
  apply Rinv_neq_0_compat.
  intro. rewrite H1 in aalt00. apply (Rlt_irrefl 0). assumption.
  rewrite H1 in r.
  apply (Rlt_irrefl vmax). assumption.
Qed.

Lemma below_vmax_upper_right_limiting_trajectory :
  forall {t1 t2 z v a} (P: Path z v a) B (M: Maneuver t1 t2 P B)
         t (tinterval : t1 <= t < t2) (zlet1 : 0 <= t1)
         (r : v t1 <= vmax B) (s : (vmax B - v t1) / (amax B) <= t-t1),
    z t <= (vmax B) * (t-t1) - ((vmax B - v t1)/(amax B)) * (vmax B - v t1)/2 + z t1.
Proof.
  ua.
  generalize (below_vmax_upper_left_limiting_trajectory P B M) as
      below_vmax_upper_left_limiting_trajectory_traj. intro.
  rewrite Bdef in below_vmax_upper_left_limiting_trajectory_traj.
  simpl in below_vmax_upper_left_limiting_trajectory_traj.
  
  generalize (pilot_model_maintains_upper_bound P B M) as pilot_model_maintains_upper_bound_traj. intro.
  rewrite Bdef in pilot_model_maintains_upper_bound_traj.
  simpl in pilot_model_maintains_upper_bound_traj.

  intros.

  assume ableamax. (* rename H into ableamax0. *)
  assume zltab. (* rename H into zltab0. *)
  assert (z ((vmax - v t1)/amax + t1) <= (vmax*vmax - (v t1)*(v t1))/(2*amax) + z t1).
  assert (0 <= (vmax - v t1) / amax). inversion_clear r.
  left. setr ((vmax - v t1) * (/ amax)).
  intro. subst. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption.
  assert (0 = 0*0). field. rewrite H0 at 1.
  apply Rmult_ge_0_gt_0_lt_compat. right. reflexivity. fourier. fourier.
  apply Rinv_0_lt_compat. fourier.
  rewrite H. setr 0.
  intro. subst. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption. right. reflexivity.
  assert ((vmax - v t1) / amax + t1 - t1 <= (vmax - v t1) / amax).
  setl ((vmax - v t1) / amax).
  intro. subst. assert (0 < 0). fourier. apply (Rlt_irrefl 0). assumption. 
  right. reflexivity.

  assert (t1 <= (vmax - v t1) / amax + t1 < t2) as vmaxinterval.
  split. Radd (-t1). setl 0. setr ((vmax - v t1) / amax).
  intro. subst. assert (0 < 0). fourier. apply (Rlt_irrefl 0). assumption. assumption.
  assert ((vmax - v t1) / amax + t1 <= t). Radd (-t1). setl ((vmax - v t1) / amax).
  intro. subst. assert (0 < 0). fourier. apply (Rlt_irrefl 0). assumption. assumption.
  set (tmp := (vmax - v t1) / amax) in *. inversion tinterval. fourier.

  generalize (below_vmax_upper_left_limiting_trajectory_traj
                ((vmax - v t1)/amax + t1) vmaxinterval zlet1 r H0). intros.
  setr (amax / 2 * (((vmax - v t1) / amax + t1 - t1) * ((vmax - v t1) / amax + t1 - t1)) +
        v t1 * ((vmax - v t1) / amax + t1 - t1) + z t1).
  intro. subst. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption. assumption.

  setr (vmax * ( (t-t1) - ((vmax - v t1)/amax)) +
        (vmax * vmax - v t1 * v t1) / (2*amax) + z t1).
  intro. subst. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption.
  set (tt := (vmax - v t1) / amax + t1).
  change (z tt <=
          (vmax * vmax - v t1 * v t1) / (2 * amax) + z t1) in H.
  assert (tt <= t) as s1. unfold tt. Radd (-t1). setr (t-t1). setl ((vmax - v t1) / amax).
  intro. rewrite H0 in ableamax0. assert (0 < 0). fourier. apply (Rlt_irrefl 0). assumption. assumption.
  Radd (- vmax * (t - tt)).
  setl (z t - vmax * (t - tt)). unfold tt at 2.
  setr ((vmax * vmax - v t1 * v t1) / (2 * amax) + z t1).
  intro. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption.
  apply (Rle_trans _ (z tt) _).

  generalize contv as contv0; intro.
  rewrite <- dpeqv in contv0.
  generalize conta as conta0; intro.
  rewrite <- dveqa in conta0.
  set (pfun := (mkC1 contv0)).
  generalize (RiemannInt_P32 pfun tt t) as vintegr. intros.
  generalize (FTC_Riemann pfun vintegr) as vintval. intros.
  simpl in vintegr, vintval.
  apply (Rplus_le_reg_l (- (z tt) + vmax * (t - tt)));
    setr (vmax * (t - tt));
    setl (z t - z tt);
  rewrite <- vintval.
  set (f := (fct_cte vmax * id)%F).
    establish_deriv2 f' (fct_cte vmax)%F f.
  rename H0 into fpf.
  assert (continuity (derive f fpf)) as contf;
    [rewrite fe; unfold f'; reg | idtac].
  set (ffun := (mkC1 contf)).
  generalize (RiemannInt_P32 ffun tt t) as fintegr; intros;
  generalize (FTC_Riemann ffun fintegr) as fintval; intros.
  setr (vmax * t - vmax * tt).
  change ( RiemannInt vintegr <= f t - f tt ).
  simpl in fintegr, fintval.
  rewrite <- fintval.
  apply RiemannInt_P19. assumption.
  intros x ttltxltt.
  assert (tt <= x <= t) as ttlexlet.
  inversion ttltxltt. split; left; assumption.
  rewrite fe, dpeqv.
  unfold f', fct_cte, mult_fct, plus_fct, id.
  assert (0 <= tt - t1) as zlettmt1. unfold tt.
  inversion_clear r.

  left.
  setr ((vmax - v t1) / amax).
  intro. assert (0 < 0). fourier. apply (Rlt_irrefl 0). assumption.
  assert (0 = 0*0). field. rewrite H1 at 1.
  apply Rmult_ge_0_gt_0_lt_compat. right. reflexivity. fourier. fourier.
  apply Rinv_0_lt_compat. fourier.
  rewrite H0. setr 0.
  intro. assert (0 < 0). fourier. apply (Rlt_irrefl 0). assumption.
  right. reflexivity. 

  assert (t1 <= t1 < t2) as t1interval. inversion tinterval. split; fourier.
  assert (t1 <= x < t2) as xinterval. inversion tinterval. inversion ttltxltt. split; fourier.
  inversion xinterval. inversion H0.
  eapply pilot_model_maintains_upper_bound_traj. apply t1interval. apply r. apply xinterval. assumption.
  rewrite <- H2. assumption.
  assumption.
Qed.

Lemma above_vmax_upper_right_limiting_trajectory :
  forall {t1 t2 z v a} (P: Path z v a) B (M: Maneuver t1 t2 P B)
         t (tinterval : t1 <= t < t2) (zlet1 : 0 <= t1)
         (r : vmax B < v t1) (s : (vmax B - v t1) / (aa B) <= t-t1),
     z t <= (vmax B) * (t-t1) - ((vmax B - v t1)/(aa B)) * (vmax B - v t1)/2 + z t1.
Proof.
  ua.
  generalize (above_vmax_upper_left_limiting_trajectory P B M) as
    above_vmax_upper_left_limiting_trajectory_traj. intro.
  rewrite Bdef in above_vmax_upper_left_limiting_trajectory_traj.
  simpl in above_vmax_upper_left_limiting_trajectory_traj.
  generalize (pilot_model_maintains_upper_bound P B M) as
    pilot_model_maintains_upper_bound_traj. intro.
  rewrite Bdef in pilot_model_maintains_upper_bound_traj.
  simpl in pilot_model_maintains_upper_bound_traj.
  generalize (pilot_model_accel_downto_limit P B M) as
    pilot_model_accel_downto_limit_traj. intro.
  rewrite Bdef in pilot_model_accel_downto_limit_traj.
  simpl in pilot_model_accel_downto_limit_traj.
  
  intros.

  assume aalt0. rename aalt1 into aalt00.
  assert (z ((vmax - v t1)/aa + t1) <= (vmax*vmax - (v t1)*(v t1))/(2*aa) + z t1).
  assert (0 <= (vmax - v t1) / aa).
  setr ((v t1 - vmax) * / - aa).
  intro. subst. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption.
  assert (0 = 0*0). field. rewrite H at 1. left.
  apply Rmult_ge_0_gt_0_lt_compat. right. reflexivity. fourier. fourier.
  apply Rinv_0_lt_compat. fourier.
  assert ((vmax - v t1) / aa + t1 -t1 <= (vmax - v t1) / aa).
  setl ((vmax - v t1) / aa).
  intro. subst. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption.
  right. reflexivity.
  assert (t1 <= (vmax - v t1) / aa + t1 < t2) as vmaxinterval.
  split. Radd (-t1). setl 0. setr ((vmax - v t1) / aa).
  intro. subst. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption. assumption.
  inversion s as [vmaxlttmt1 | vmaxeqtmt1].
  inversion tinterval. apply (Rlt_trans _ t  _).
  Radd (-t1). setr (t-t1). setl ((vmax - v t1) / aa).
  intro. subst. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption. assumption. assumption.
  rewrite vmaxeqtmt1. setl t. inversion tinterval. assumption.
  generalize (above_vmax_upper_left_limiting_trajectory_traj
                ((vmax - v t1)/aa + t1) vmaxinterval zlet1 r H0). intros.
  setr (aa / 2 * (((vmax - v t1) / aa + t1 - t1) * ((vmax - v t1) / aa + t1 - t1)) +
        v t1 * ((vmax - v t1) / aa + t1 - t1) + z t1).
  intro. subst. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption. assumption.

  setr (vmax * ( (t-t1) - ((vmax - v t1)/aa)) +
        (vmax * vmax - v t1 * v t1) / (2*aa) + z t1).
  intro. subst. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption.
  set (tt := (vmax - v t1) / aa + t1).
  change (z tt <= 
          (vmax * vmax - v t1 * v t1) / (2 * aa) + z t1) in H.
  assert (tt <= t) as s1.
  unfold tt. Radd (-t1). setr (t-t1). setl ((vmax - v t1) / aa).
  intro. rewrite H0 in aalt00. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption. assumption.
  Radd (- vmax * (t - tt)). unfold tt at 2.
  setr ((vmax * vmax - v t1 * v t1) / (2 * aa) + z t1).
  intro. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption.
  setl (z t - vmax * (t - tt)).
  apply (Rle_trans _ (z tt) _).

  generalize contv as contv0; intro.
  rewrite <- dpeqv in contv0.
  generalize conta as conta0; intro.
  rewrite <- dveqa in conta0.
  set (pfun := (mkC1 contv0)).
  generalize (RiemannInt_P32 pfun tt t) as vintegr. intros.
  generalize (FTC_Riemann pfun vintegr) as vintval. intros.
  simpl in vintegr, vintval.
  apply (Rplus_le_reg_l (- (z tt) + vmax * (t - tt)));
    setr (vmax * (t - tt));
    setl (z t - z tt).
  rewrite <- vintval.
  set (f := (fct_cte vmax * id)%F).
    establish_deriv2 f' (fct_cte vmax)%F f.
  rename H0 into fpf.
  assert (continuity (derive f fpf)) as contf;
    [rewrite fe; unfold f'; reg | idtac].
  set (ffun := (mkC1 contf)).
  generalize (RiemannInt_P32 ffun tt t) as fintegr; intros;
  generalize (FTC_Riemann ffun fintegr) as fintval; intros.
  setr (vmax * t - vmax * tt).
  change (RiemannInt vintegr <=  f t - f tt).
  simpl in fintegr, fintval.
  rewrite <- fintval.
  apply RiemannInt_P19. assumption.
  intros x ttltxltt.
  assert (tt <= x <= t) as ttlexlet.
  inversion ttltxltt. split; left; assumption.
  rewrite fe, dpeqv.
  unfold f', fct_cte, mult_fct, plus_fct, id.
  assert (0 < tt - t1 <= (vmax - v t1) / aa) as ttpos.

  split.
  unfold tt.
  setr ((v t1 - vmax ) * / - aa).
  intro. rewrite H0 in aalt00. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption.
  assert (0 = 0*0). field. rewrite H0 at 1. 
  apply Rmult_ge_0_gt_0_lt_compat. right. reflexivity. fourier. fourier.
  apply Rinv_0_lt_compat. fourier.
  Radd t1.
  setl tt. unfold tt. right. reflexivity.

  assert ( v tt <= aa * (tt - t1) + v t1) as vttval.
  Radd (- v t1). setr (aa * (tt - t1)). setl (v tt - v t1).
  assert (t1 <= t1 < t2) as t1interval. inversion tinterval. split; fourier.
  assert (t1 <= tt < t2) as ttinterval. split.
  inversion ttpos. left. fourier. inversion ttltxltt. inversion tinterval. fourier.

  apply (pilot_model_accel_downto_limit_traj t1 t1interval r tt ttinterval ttpos).
  
  assert (aa * ((vmax - v t1) / aa + t1 - t1) + v t1 = vmax).
  field.
  intro. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption.
  change (aa * (tt - t1) + v t1 = vmax) in H0.
  rewrite H0 in vttval.

  assert (t1 <= tt < t2) as ttinterval. inversion ttpos. inversion tinterval. split; fourier.
  assert (t1 <= x < t2) as xinterval. inversion tinterval. inversion ttltxltt. inversion ttpos.
  split; fourier.
  inversion xinterval.
  eapply pilot_model_maintains_upper_bound_traj. apply ttinterval. assumption. apply xinterval.
  inversion_clear ttltxltt. assumption.
  assumption.

Qed.

Lemma bounded_above :
    forall {t1 t2 z v a} (P: Path z v a) B (M: Maneuver t1 t2 P B)
         t (tinterval : t1 <= t < t2) (zlet1 : 0 <= t1),
    (* K amin ab (v 0) vmin (z 0) t <= *) z t <= K (aa B) (amax B) (v t1) (vmax B) (z t1) (t-t1).
Proof.
  ua.
  generalize (above_vmax_upper_left_limiting_trajectory P B M) as 
    above_vmax_upper_left_limiting_trajectory_traj. intro.
  rewrite Bdef in     above_vmax_upper_left_limiting_trajectory_traj.
  simpl in     above_vmax_upper_left_limiting_trajectory_traj.
  generalize (above_vmax_upper_right_limiting_trajectory P B M) as 
    above_vmax_upper_right_limiting_trajectory_traj. intro.
  rewrite Bdef in     above_vmax_upper_right_limiting_trajectory_traj.
  simpl in     above_vmax_upper_right_limiting_trajectory_traj.
  generalize (below_vmax_upper_left_limiting_trajectory P B M) as 
    below_vmax_upper_left_limiting_trajectory_traj. intro.
  rewrite Bdef in     below_vmax_upper_left_limiting_trajectory_traj.
  simpl in     below_vmax_upper_left_limiting_trajectory_traj.
  generalize (below_vmax_upper_right_limiting_trajectory P B M) as 
    below_vmax_upper_right_limiting_trajectory_traj. intro.
  rewrite Bdef in     below_vmax_upper_right_limiting_trajectory_traj.
  simpl in     below_vmax_upper_right_limiting_trajectory_traj.
  
  intros.
  assume aalt0. rename aalt1 into aalt00.
  assume ableamax. (* rename H into ableamax0. *)
  assume zltab. (* rename H into zltab0. *)


  unfold K.
  destruct (total_order_T vmax (v t1)); [
      assert (vmax <= v t1) as r; [inversion s ;
                                   [ left; assumption | right ; assumption] |
                                  idtac]; clear s |
      idtac]; [
  destruct (total_order_T (t-t1) ((vmax - v t1) / aa)); [
      assert (t-t1 <= (vmax - v t1) / aa) as s0; [inversion s ;
                                   [ left; assumption | right ; assumption] |
                                  idtac]; clear s |
      idtac] |
  destruct (total_order_T (t-t1) ((vmax - v t1) / amax)); [
      assert (t-t1 <= (vmax - v t1) / amax) as s0; [inversion s ;
                                   [ left; assumption | right ; assumption] |
                                  idtac]; clear s |
      idtac]];
    unfold J;
    simpl.

  setr (aa / 2 * ((t-t1) * (t-t1)) + v t1 * (t-t1) + z t1).
  rename r into vmpos.
  inversion_clear vmpos as [r|r].
  apply above_vmax_upper_left_limiting_trajectory_traj; try assumption.
  assert (t-t1 <= 0) as tle0. rewrite r in s0.
  setr ((v t1 - v t1)/aa).
  intro. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption. assumption.

  assert (0 <= t-t1) as zletmt1. inversion tinterval. fourier.
  inversion tle0 as [tlt0 | teq0]. apply False_ind.
  eapply Rge_not_lt. apply Rle_ge. apply zletmt1. assumption.
  rewrite teq0. setr (z t1).
  assert (t=t1) as teqt1. Radd (-t1). setl (t-t1). setr 0. assumption.
  rewrite teqt1.
  right. reflexivity.

  setr (vmax * (t-t1) - (vmax - v t1) / aa * (vmax - v t1) / 2 + z t1).
  intro. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption.
  rename r into vmpos.
  inversion_clear vmpos as [r|r].
  apply above_vmax_upper_right_limiting_trajectory_traj; try assumption.
  left. assumption.

  assert (vmax - v t1 = 0) as zer.
  Radd (v t1). setl vmax. setr (v t1). assumption.

  assert (v t1 <= vmax) as v0levm. right. symmetry. assumption.
  assert ((vmax - v t1)/amax <= t-t1) as tgett. left. rewrite zer in *.
  setl 0.
  intro. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption.
  assert (0 / aa = 0) as zltaa. field.
  intro. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption.
  rewrite zltaa in r0. assumption.

  generalize (below_vmax_upper_right_limiting_trajectory_traj
                t tinterval zlet1 v0levm tgett) as bnd. intros.
  rewrite zer in *.
  fieldrewrite (vmax * (t-t1) - 0 / aa * 0 / 2 + z t1)
               (vmax * (t-t1) + z t1).
  intro. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption.

  assert (vmax * (t-t1) - 0 / amax * 0 / 2 + z t1 = vmax * (t-t1) + z t1) as bndeq.
  field.
  intro. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption.
  rewrite bndeq in bnd. assumption.

  setr (amax / 2 * ((t-t1) * (t-t1)) + v t1 * (t-t1) + z t1).
  apply below_vmax_upper_left_limiting_trajectory_traj; try assumption.
  left. assumption.
  setr (vmax * (t-t1) - (vmax - v t1) / amax * (vmax - v t1) / 2 + z t1).
  intro. rewrite H in ableamax0. assert (0 < 0). fourier.
  apply (Rlt_irrefl 0). assumption.
  apply below_vmax_upper_right_limiting_trajectory_traj; try assumption.
  left. assumption.
  left. assumption.
Qed.

(* End Trajectory. *)


(* When putting everything together, remember: K and Φ are
indexed from time zero in the polynomial, which we align with the
beginning of the maneuver. They have no absolute time reference, so
they need a -t1 adjustment (e.g. becomes t-t1) in their arguments. The
rest of our state such as z v a, all have an absolute time reference,
so they use t without adjustment. *)


(*
Two aircraft with paths Po and Pi, undergoing maneuvers Mo and Mi
respectively during time interval [t1,t2], which are in horizontal
conflict during time interval [tb,te] are safely separated during
[t1,t2] because the Po aircraft is above the Pi aircraft, separated by
at least distance hp.
*)
Lemma safely_above_for_1_maneuver :
  forall {t tb te hp t1 t2 zo vo ao zi vi ai Bo Bi}
         (Po: Path zo vo ao) (Mo: Maneuver t1 t2 Po Bo)
         (Pi: Path zi vi ai) (Mi: Maneuver t1 t2 Pi Bi)
    (t1ge0 : 0 <= t1)
    (tmaneuver : t1 <= t < t2)
    (thconflict : tb <= t <= te),
    Φ (amin Bo) (ab Bo) (vo t1) (vmin Bo) (zo t1)
              (aa Bi) (amax Bi) (vi t1) (vmax Bi) (zi t1) hp (tb-t1) (te-t1) ->
    hp < zo t - zi t.
Proof.
  intros.
  rename H into vs.

  generalize (bounded_below Po Bo Mo t tmaneuver t1ge0) as ownbb. intros.
  generalize (bounded_above Pi Bi Mi t tmaneuver t1ge0) as intba. intros.
  
  apply (Rlt_le_trans _
                      (K (amin Bo) (ab Bo) (vo t1) (vmin Bo) (zo t1) (t-t1) -
                       K (aa Bi) (amax Bi) (vi t1) (vmax Bi) (zi t1) (t-t1))
                      _).

  apply (safely_separated_trajectory_interval_above
                 (amin Bo) (ab Bo) (vo t1) (vmin Bo) (zo t1)
                 (aa Bi) (amax Bi) (vi t1) (vmax Bi) (zi t1)
                 hp (tb-t1) (te-t1)); try assumption.
  inversion thconflict.
  split. Radd t1. setl tb. setr t. assumption.
  Radd t1. setl t. setr te. assumption.
  apply Rplus_le_compat; try assumption.
  apply Ropp_le_contravar; try assumption.
Qed.

(* The assertion that a pair of aircraft are vertically safe *)


(* This predicate describes a pair of aircraft following paths Po and
Pi, and an arbitrary sequence of maneuvers that satisfy our safety
predicates, where the Po aircraft is above the Pi aircraft. *)

Inductive SafeFlt {zo vo ao zi vi ai} t1 tb te hp
          (Po: Path zo vo ao) (Pi: Path zi vi ai) :Prop :=
| trj_intro : forall t2 Bo Bi,
    Maneuver t1 t2 Po Bo -> 
    Maneuver t1 t2 Pi Bi -> 
    Φ (amin Bo) (ab Bo) (vo t1) (vmin Bo) (zo t1)
              (aa Bi) (amax Bi) (vi t1) (vmax Bi) (zi t1)
              hp (Rmax (0-t1) (tb-t1)) (Rmin (t2-t1) (te-t1)) ->
    SafeFlt t2 tb te hp Po Pi ->
    SafeFlt t1 tb te hp Po Pi
| trj_null : forall Bo Bi,
    TailManeuver t1 Po Bo ->
    TailManeuver t1 Pi Bi ->
    Φ (amin Bo) (ab Bo) (vo t1) (vmin Bo) (zo t1)
              (aa Bi) (amax Bi) (vi t1) (vmax Bi) (zi t1)
              hp (Rmax (0-t1) (tb-t1)) (te-t1) ->
    SafeFlt t1 tb te hp Po Pi.

Definition P {zo vo ao zi vi ai} t1 tb te hp (Po: Path zo vo ao) (Pi: Path zi vi ai) :=
  forall t : R, 0 <= t1 -> Rmax t1 tb <= t <= te -> hp < zo t - zi t.

(*
Two aircraft with paths Po and Pi, each of which follows an arbitrary sequence
of independent maneuvers, where the motion of each aircraft for each
maneuver separately satisfies our safety predicate, and whose
horizontal motion create a single horizontal conflict interval from
[tb,te] are safely separated for all time because the Po aircraft is
always above the Pi aircraft by at least a distance hp.
*)
Lemma safely_above_for_m_maneuvers : (* index o above i *)
  forall {zo vo ao zi vi ai}
             t1 tb te hp
         (Po: Path zo vo ao) (Pi: Path zi vi ai)
         (F : SafeFlt t1 tb te hp Po Pi),
  forall t
         (t1ge0 : 0 <= t1)
         (thconflict : (Rmax t1 tb) <= t <= te),
    hp < zo t - zi t.
Proof.
  intros zo vo ao zi vi ai.
  apply (SafeFlt_ind zo vo ao zi vi ai P).

  (* inductive step Pi->Pi+1 *)
  intros until 0. intros Mo Mi vs Ft2 Pt2. unfold P in *.
  inversion Mo. clear vabove vatupper vwithin vatlower vbelow.
  intros t zlet1 tinterval.
  unfold Rmax, Rmin in *.
  destruct (Rle_dec t1 tb).
  destruct (Rle_dec t2 tb).
  assert (0 <= t2) as zlet2. fourier.
  apply (Pt2 t zlet2 tinterval).
  generalize (Rnot_le_gt _ _ n) as tbltt2; intros; clear n.
  apply Rgt_lt in tbltt2.
  generalize (Rtotal_order t t2) as trelt2'. intros.
  inversion trelt2' as [trelt2 | trelt2]; clear trelt2'.
  (****** use Φ **********************)
  assert (tb <= t <= t2) as tsubinterval. inversion tinterval. split; fourier.
  assert (t1 <= t < t2) as tmaneuver. inversion tinterval. split; fourier.
  destruct (Rle_dec (0 - t1) (tb - t1)).
  destruct (Rle_dec (t2 - t1) (te - t1)).
  apply (safely_above_for_1_maneuver Po Mo Pi Mi zlet1 tmaneuver tsubinterval vs).
  apply (safely_above_for_1_maneuver Po Mo Pi Mi zlet1 tmaneuver tinterval vs).
  apply False_ind.
  apply n. Radd t1. setl 0. setr tb. fourier.
  (****************************)
  assert (t2 <= t <= te) as tsubinterval. inversion tinterval.
  split. inversion trelt2. rewrite H1. right. reflexivity. left. fourier. assumption.
  clear trelt2. assert (0 <= t2) as zlet2. fourier.
  apply (Pt2 t zlet2 tsubinterval).

  destruct (Rle_dec t2 tb).
  generalize (Rnot_le_gt _ _ n) as tbltt1; intros; clear n.
  apply Rgt_lt in tbltt1.
  assert (t1>t2). fourier.
  generalize (Rgt_not_le _ _ H).
  intro. apply False_ind. apply H0. assumption.
  generalize (Rnot_le_gt _ _ n) as tbltt1; intros; clear n.
  apply Rgt_lt in tbltt1.
  generalize (Rnot_le_gt _ _ n0) as t2lttb; intros; clear n0.
  apply Rgt_lt in t2lttb.

  generalize (Rtotal_order t t2) as trelt2'. intros.
  inversion trelt2' as [trelt2 | trelt2]; clear trelt2'.
  (****** use Φ **********************)
  assert (tb <= t <= t2) as tsubinterval. inversion tinterval. split; fourier.
  assert (tb <= t <= te) as tsubinterval2. inversion tinterval. split; fourier.
  assert (t1 <= t < t2) as tmaneuver. inversion tinterval. split; fourier.
  assert (0 <= t <= t2) as tsubinterval3. inversion tinterval. split; fourier.
  assert (0 <= t <= te) as tsubinterval4. inversion tinterval. split; fourier.
  destruct (Rle_dec (0 - t1) (tb - t1)).
  destruct (Rle_dec (t2 - t1) (te - t1)).
  
  apply (safely_above_for_1_maneuver Po Mo Pi Mi zlet1 tmaneuver tsubinterval vs).
  apply (safely_above_for_1_maneuver Po Mo Pi Mi zlet1 tmaneuver tsubinterval2 vs).
  destruct (Rle_dec (t2 - t1) (te - t1)).
  apply (safely_above_for_1_maneuver Po Mo Pi Mi zlet1 tmaneuver tsubinterval3 vs).
  apply (safely_above_for_1_maneuver Po Mo Pi Mi zlet1 tmaneuver tsubinterval4 vs).
  (****************************)
  assert (t2 <= t <= te) as tsubinterval. inversion tinterval.
  split. inversion trelt2. rewrite H1. right. reflexivity. left. fourier. assumption.
  clear trelt2. assert (0 <= t2) as zlet2. fourier.
  apply (Pt2 t zlet2 tsubinterval).

  (* base case P0 *)
  intros until 0. intros Mo Mi vs.
  unfold P.
  intros t zlet1 tinterval.
  unfold Rmax in *.
  destruct (Rle_dec t1 tb).
  assert (t1 <= t < te+1) as tsubinterval. inversion tinterval. split; fourier.
  inversion_clear Mo. generalize (mnv (te+1)) as mnv'; clear mnv; intro.
  inversion_clear Mi. generalize (mnv (te+1)) as mnv0'; clear mnv; intro.
  destruct (Rle_dec (0-t1) (tb-t1)). clear r0.
  apply (safely_above_for_1_maneuver Po mnv' Pi mnv0' zlet1 tsubinterval tinterval vs).
  assert (0 <= t <= te) as tinterval2. inversion tinterval. split; fourier.
  apply (safely_above_for_1_maneuver Po mnv' Pi mnv0' zlet1 tsubinterval tinterval2 vs).
  
  generalize (Rnot_le_gt _ _ n) as tbltt1; intros; clear n.
  apply Rgt_lt in tbltt1.
  destruct (Rle_dec (0-t1) (tb-t1)).

  assert (0 <= tb) as t1letb. fourier. clear r.
  assert (tb <= t <= te) as tsubinterval4. inversion tinterval. split; fourier.
  assert (t1 <= t < (te+1)) as tsubinterval5. inversion tinterval. split; fourier.
  inversion_clear Mo. generalize (mnv (te+1)) as mnv'; clear mnv; intro.
  inversion_clear Mi. generalize (mnv (te+1)) as mnv0'; clear mnv; intro.
  apply (safely_above_for_1_maneuver Po mnv' Pi mnv0' zlet1 tsubinterval5 tsubinterval4 vs).

  assert (0 <= t <= te) as tsubinterval4. inversion tinterval. split; fourier.
  assert (t1 <= t < (te+1)) as tsubinterval5. inversion tinterval. split; fourier.
  inversion_clear Mo. generalize (mnv (te+1)) as mnv'; clear mnv; intro.
  inversion_clear Mi. generalize (mnv (te+1)) as mnv0'; clear mnv; intro.
  apply (safely_above_for_1_maneuver Po mnv' Pi mnv0' zlet1 tsubinterval5 tsubinterval4 vs).
Qed.

(*
This predicate describes a pair of aircraft following paths Po and
Pi, and an arbitrary sequence of maneuvers that satisfy our safety
predicates.
*)

Definition SafeFltAB {zo vo ao zi vi ai} t1 tb te hp
           (Po: Path zo vo ao) (Pi: Path zi vi ai) :=
  SafeFlt t1 tb te hp Po Pi \/ SafeFlt t1 tb te hp Pi Po.


(*
Two aircraft with paths Po and Pi, each of which follows an
arbitrary sequence of independent maneuvers, where the motion of each
aircraft for each maneuver separately satisfies our safety predicate,
and whose horizontal motion create a single horizontal conflict
interval from [tb,te] are safely separated vertically for all time by
at least a distance hp.
*)

Lemma own_safe_for_m_maneuvers :
  forall {zo vo ao zi vi ai}
         t1 tb te hp
         (hppos : 0 < hp)
         (Po: Path zo vo ao) (Pi: Path zi vi ai)
         (F : SafeFltAB t1 tb te hp Po Pi),
  forall t
         (t1ge0 : 0 <= t1)
         (thconflict : (Rmax t1 tb) <= t <= te),
    hp < Rabs (zo t - zi t).
Proof.
  intros.
  unfold SafeFltAB in F.
  inversion_clear F.
  generalize (safely_above_for_m_maneuvers t1 tb te hp Po Pi
                                           H t t1ge0 thconflict).
  intros. assert (zo t > zi t) as order. fourier.
  unfold Rabs.
  destruct (Rcase_abs (zo t - zi t)).
  apply False_ind.
  assert (zo t <= zi t). fourier.
  eapply Rlt_not_le. apply order. assumption.
  assumption.

  generalize (safely_above_for_m_maneuvers t1 tb te hp Pi Po
                                           H t t1ge0 thconflict).
  intros. assert (zo t < zi t) as order. fourier.
  unfold Rabs.
  destruct (Rcase_abs (zo t - zi t)).
  setr (zi t - zo t).
  assumption.
  apply False_ind.
  assert (zi t <= zo t). fourier.
  eapply Rlt_not_le. apply order. assumption.
Qed.

(*
This predicate says if our aircraft follows path Po, and there are a
sequence of other paths possibly belonging to multiple aircraft who
come into horizontal conflict with us at a sequence of different time
intervals, where the motion of each aircraft for each maneuver
separately satisfies the safety predicate for us, the Pi aircraft is
safely separated from all the others vertically by at least a distance
hp during the horizontal conflict intervals guaranteeing no collisions.
*)

Record CI  := { tb:R; te:R; zi:R->R; vi:R->R; ai:R->R; Pi:Path zi vi ai}.

Inductive Ψ {zo vo ao } t1 hp
          (Po: Path zo vo ao) : list CI -> Prop :=
| mtrj_intro : forall (q:CI) (r:list CI),
    SafeFltAB t1 (tb q) (te q) hp Po (Pi q) ->
    Ψ t1 hp Po r ->
    Ψ t1 hp Po (q::r)
| mtrj_null : Ψ t1 hp Po List.nil.


Inductive SeparateMulti {zo vo ao} t1 hp
          (Po: Path zo vo ao) : list CI -> Prop :=
| smtrj_intro : forall (q:CI) (r:list CI),
    (forall t, (Rmax t1 (tb q)) <= t <= (te q) ->
    hp < Rabs (zo t - (zi q) t)) ->
    SeparateMulti t1 hp Po r ->
    SeparateMulti t1 hp Po (q::r)
| smtrj_null : SeparateMulti t1 hp Po List.nil.


(* equation 10 in vert-paper.pdf *)
Theorem safely_separated_vertical_trajectories:
  forall {zo vo ao} t1 hp cilst
         (Po: Path zo vo ao) (hppos : 0 < hp) (t1pos : 0 <= t1),
    Ψ t1 hp Po cilst ->
    SeparateMulti t1 hp Po cilst.
Proof.
  intros until 0. intros hppos t1pos sfm.
  induction cilst.
  apply smtrj_null.
  inversion_clear sfm. 
  destruct a0. apply smtrj_intro.
  simpl in *.
  (*************)
  clear H0 IHcilst cilst.
  intros.
  apply (own_safe_for_m_maneuvers
         t1 tb0 te0 hp hppos Po Pi0 H t t1pos H0).
  (*************)
  apply IHcilst; try assumption.
Qed.

