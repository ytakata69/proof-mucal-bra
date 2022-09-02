(*
 * mu-calculus for infinite data words:
 * Definitions about Buchi automata
 *)

Require Import ltl.

(* The set of actions with epsilon *)
Inductive SigmaE :=
  | epsilon
  | Σφ (phi : ltl_phi)
  .

Record automaton : Type :=
  mk_automaton {
    states : Set;
    transitions : states -> SigmaE -> list register -> states -> Prop;
    finals : states -> Prop
  }.

(* The set of configurations of A *)
Definition config (A : automaton) :=
  (states A * Theta * nat)%type.

Inductive move {A : automaton}
  : config A -> config A -> Prop :=
  | move_action :
    forall phi R i q1 q2 th,
    transitions A q1 (Σφ phi) R q2 ->
    models_phi i th phi ->
    move (q1, th, i)
         (q2, (updateR th R (snd (Str_nth i w))), (S i))
  | move_epsilon :
    forall i q1 q2 th,
    transitions A q1 epsilon nil q2 ->
    move (q1, th, i) (q2, th, i)
  .

Inductive moveStar {A : automaton}
  : config A -> config A -> Prop :=
  | moveStar_refl : forall c1,
    moveStar c1 c1
  | move_moveStar : forall c1 c2 c3,
    move c1 c2 -> moveStar c2 c3 -> moveStar c1 c3
  .

Lemma moveStar_transitive {A : automaton} :
  forall c1 c2 c3 : config A,
  moveStar c1 c2 -> moveStar c2 c3 ->
  moveStar c1 c3.
Proof.
  intros c1 c2 c3 H12 H13.
  induction H12; auto.
  apply move_moveStar with c2; auto.
Qed.

Lemma moveStar_move {A : automaton} :
  forall c1 c2 c3 : config A,
  moveStar c1 c2 -> move c2 c3 ->
  moveStar c1 c3.
Proof.
  intros c1 c2 c3 H12 H23.
  apply moveStar_transitive with c2; auto.
  apply move_moveStar with c3; auto.
  apply moveStar_refl.
Qed.

CoInductive acceptingLoop {A : automaton} : config A -> Prop :=
  acceptingLoop_intro : forall q th1 th2 i j,
    finals A q ->
    i < j ->
    moveStar (q, th1, i) (q, th2, j) ->
    acceptingLoop (q, th2, j) ->
    acceptingLoop (q, th1, i).

Inductive accepting {A : automaton} : config A -> Prop :=
  accepting_intro : forall q1 q2 th1 th2 i j,
    i < j ->
    moveStar (q1, th1, i) (q2, th2, j) ->
    acceptingLoop (q2, th2, j) ->
    accepting (q1, th1, i).

(* Conversion from Eqn into BRA *)

Inductive RuleA (sigma : eqn_sys)
  : ltl -> SigmaE -> list register -> ltl -> Prop :=
  | RuleA_TT :
    RuleA sigma (φ [tt]) (Σφ [tt]) nil (φ [tt])
  | RuleA_OR_left :
    forall v1 v2 : Var,
    RuleA sigma (var v1 .\/ var v2) epsilon nil (sigma v1)
  | RuleA_OR_right :
    forall v1 v2 : Var,
    RuleA sigma (var v1 .\/ var v2) epsilon nil (sigma v2)
  | RuleA_STORE_X :
    forall R (v : Var) (phi : ltl_phi),
    RuleA sigma (↓ R ,X (var v) ../\ phi) (Σφ phi) R (sigma v)
  .

Inductive FinalA (sigma : eqn_sys)
  : ltl -> Prop :=
  | FinalA_TT  : FinalA sigma (φ [tt])
  | FinalA_Var_omega : forall v : Var,
    Var_omega v = true -> FinalA sigma (sigma v)
  .

Definition EqnBRA (sigma : eqn_sys) :=
  mk_automaton ltl (RuleA sigma) (FinalA sigma).

Section CorrectnessOfEqnBRA.

Variable sigma : eqn_sys.
Local Definition A := EqnBRA sigma.

Lemma tt_loop_exists :
  forall theta i j,
  i <= j ->
  moveStar (A:=A) (φ [tt], theta, i) (φ [tt], theta, j).
Proof.
  intros theta i j Hij.
  induction Hij as [| j Hij IH].
  - apply moveStar_refl.
  - apply moveStar_move with (φ [tt], theta, j);
  auto.
  assert (not_update : forall d, theta = updateR theta nil d).
  { now unfold updateR. }
  rewrite (not_update (snd (Str_nth j w))) at 2.
  apply @move_action with (A := A) (phi := [tt]).
  + apply RuleA_TT.
  + apply models_pos.
  now unfold models_atom.
Qed.

Lemma tt_loop_keeps_registers :
  forall theta theta' i j q,
  moveStar (A:=A) (φ [tt], theta, i) (q, theta', j)
  -> q = (φ [tt]) /\ theta = theta'.
Proof.
  intros theta theta' i j q H.
  remember (φ [tt], theta, i) as c1 eqn: EQc1.
  remember (q, theta', j) as c2 eqn: EQc2.
  generalize dependent theta;
  generalize dependent i.
  generalize dependent theta';
  generalize dependent j;
  generalize dependent q.
  induction H as [c1 | c1 c3 c2 Hmov Hstar IH];
  intros q j theta' EQc2 i theta EQc1.
  - (* When c1 = c2 *)
  split;
  rewrite EQc2 in EQc1;
  now inversion EQc1.
  - (* When move c1 c3 and moveStar c3 c2 *)
  rewrite EQc2 in Hstar;
  rewrite EQc2 in IH;
  clear c2 EQc2.
  rewrite EQc1 in Hmov;
  clear c1 EQc1.
  specialize (IH q j theta' (refl_equal (q, theta', j))).

  destruct c3 as [[q3 th3] i3].
  inversion Hmov
    as [phi R i1 q1 q2 th Ht Hm [EQq1 EQth EQi1] [EQq2 EQth3 EQi3]
       |i1 q1 q2 th Ht [EQq1 EQth EQi1] [EQq2 EQth3 EQi3]];
  clear i1 EQi1 q1 EQq1 q2 EQq2;
  inversion Ht as [EQtt EQphi EQR EQq3| | |];
  clear EQtt.
  rewrite <- EQR in EQth3;
  clear Ht R EQR.
  rewrite updateR_nil in EQth3.
  rewrite <- EQth3 in IH;
  rewrite <- EQth3 in Hstar;
  rewrite <- EQth3 in Hmov;
  clear th3 EQth3.
  rewrite <- EQq3 in IH;
  rewrite <- EQq3 in Hstar;
  rewrite <- EQq3 in Hmov;
  clear q3 EQq3.
  rewrite <- EQi3 in IH;
  rewrite <- EQi3 in Hstar;
  rewrite <- EQi3 in Hmov;
  clear i3 EQi3.
  specialize (IH (S i) theta (refl_equal (φ [tt], theta, S i))).
  assumption.
Qed.

Lemma move_must_go_forward :
  forall i j q1 q2 theta1 theta2,
  move (A:=A) (q1, theta1, i) (q2, theta2, j)
  -> i <= j.
Proof.
  intros i j q1 q2 th1 th2 Hm.
  inversion Hm; auto.
Qed.

Lemma moveStar_must_go_forward :
  forall i j q1 q2 theta1 theta2,
  moveStar (A:=A) (q1, theta1, i) (q2, theta2, j)
  -> i <= j.
Proof.
  intros i j q1 q2 th1 th2 Hm.
  remember (q1, th1, i) as c1 eqn: EQc1.
  remember (q2, th2, j) as c2 eqn: EQc2.
  generalize dependent th2.
  generalize dependent q2.
  generalize dependent th1.
  generalize dependent q1.
  generalize dependent i.
  induction Hm as [| c1 c3 c2 Hmov Hstar IH];
  intros i q1 th1 EQc1 q2 th2 EQc2.
  - rewrite EQc2 in EQc1.
  inversion EQc1; auto.
  - destruct c3 as [[q3 th3] i3].
  apply le_trans with i3.
  + rewrite EQc1 in Hmov.
  now apply move_must_go_forward with q1 q3 th1 th3.
  + apply IH with q3 th3 q2 th2; auto.
Qed.

Hypothesis Hnormal :
  forall v : Var, isNormal (sigma v).

Lemma x_is_either_tt_or_Var_omega :
  forall x v i j theta theta',
  (exists ell : nat,
    (i, theta; j, theta', x |= Fpow_emp sigma ell, var v)) ->
  x = Vtt \/ Var_omega x = true.
Proof.
  intros x v i j theta theta';
  intros [ell H];
  revert x v i j theta theta' H.
  induction ell as [| n IHn].
  - (* When ell = 0 *)
  unfold Fpow_emp.
  unfold Fpow.
  intros x v i j theta theta' H.
  inversion_clear H as [i1 j1 t1 t2 x1 v1 _ Hu| | | |].
  inversion Hu.
  - (* When ell = S n *)
  unfold Fpow_emp.
  intros x v i j theta theta' H.
  inversion_clear H as [i1 j1 t1 t2 x1 v1 Hij Hu| | | |].
  inversion Hu as [Hm | Hm].
  + (* When (i,theta;j,theta',x |= sigma v) *)
  assert (Hn := Hnormal v).
  destruct Hn as [v1 v2 | R v1 phi |].
  * (* When sigma v = var v1 .\/ var v2 *)
  inversion_clear Hm as [| i1 i2 t1 t2 x1 p1 p2 _ Hm' | | |].
  destruct Hm' as [Hm' | Hm'].
  -- now apply IHn with v1 i j theta theta'.
  -- now apply IHn with v2 i j theta theta'.
  * (* When sigma v = ↓ R ,X var v1 ../\ phi *)
  inversion Hm;
  now apply IHn with v1 (S i) j (updateR theta R (snd (Str_nth i w))) theta'.
  * (* When sigma v = φ [tt] *)
  inversion Hm;
  left;
  reflexivity.
  + (* When Var_omega v = true /\ x = v *)
  destruct Hm as [Homega [EQxv _]].
  rewrite EQxv; auto.
Qed.

Lemma tt_Var_omega_FinalA :
  forall x,
  x = Vtt \/ Var_omega x = true ->
  FinalA sigma (sigma x).
Proof.
  intros x [H | H].
  - rewrite H.
  rewrite sigma_Vtt;
  apply FinalA_TT.
  - apply FinalA_Var_omega;
  assumption.
Qed.

Lemma sigma_fin_leq_EqnBRA :
  forall x v i j theta theta',
  (exists ell : nat,
    (i, theta; j, theta', x |= Fpow_emp sigma ell, var v)) ->
  moveStar (A:=A) (sigma v, theta, i) (sigma x, theta', j).
Proof.
  intros x v i j theta theta';
  intros [ell H];
  revert x v i j theta theta' H.
  induction ell as [| n IHn].
  - (* When ell = 0 *)
  unfold Fpow_emp.
  unfold Fpow.
  intros x v i j theta theta' H.
  inversion_clear H as [i1 j1 t1 t2 x1 v1 _ Hu| | | |].
  inversion Hu.
  - (* When ell = S n *)
  unfold Fpow_emp.
  intros x v i j theta theta' H.
  inversion_clear H as [i1 j1 t1 t2 x1 v1 Hij Hu| | | |].
  inversion Hu as [Hm | Hm].
  + (* When (i,theta;j,theta',x |= sigma v) *)
  assert (Hn := Hnormal v).
  remember (sigma v) as sv eqn: EQsv.
  destruct Hn as [v1 v2 | R v1 phi |].
  * (* When sigma v = var v1 .\/ var v2 *)
  inversion_clear Hm as [| i1 i2 t1 t2 x1 p1 p2 _ Hm' | | |].
  destruct Hm' as [Hm' | Hm'].
  -- apply move_moveStar with (c2 := (sigma v1, theta, i)).
  ++ apply @move_epsilon with (A:=A);
  apply RuleA_OR_left.
  ++ now apply IHn.
  -- apply move_moveStar with (c2 := (sigma v2, theta, i)).
  ++ apply @move_epsilon with (A:=A);
  apply RuleA_OR_right.
  ++ now apply IHn.
  * (* When sigma v = ↓ R ,X var v1 ../\ phi *)
  inversion Hm.
  assert (Hmv : move (A:=A)
    (↓ R ,X var v1 ../\ phi, theta, i)
    (sigma v1, updateR theta R (snd (Str_nth i w)), S i)).
  { apply @move_action with (A:=A) (phi:=phi).
  - apply RuleA_STORE_X.
  - assumption.
  }
  apply move_moveStar with (c2:=(sigma v1, updateR theta R (snd (Str_nth i w)), S i));
  auto.
  * (* When sigma v = φ [tt] *)
  inversion_clear Hm;
  rewrite sigma_Vtt;
  apply tt_loop_exists;
  assumption.
  + (* When Var_omega v = true /\ x = v *)
  destruct Hm as [Homega [EQxv [EQij EQth]]];
  rewrite EQxv;
  rewrite EQij;
  rewrite EQth;
  apply moveStar_refl.
Qed.

(*
Hypothesis tt_Vtt : forall v,
  sigma v = (φ [tt]) -> v = Vtt.

Hypothesis Var_omega_Vtt :
  Var_omega Vtt = true.

Hypothesis sigma_Var_omega :
  forall v1 v2,
  sigma v1 = sigma v2 ->
  Var_omega v1 = true ->
  Var_omega v2 = true.
*)

Hypothesis sigma_injective_on_Var_omega :
  forall v1 v2,
  Var_omega v1 = true ->
  sigma v1 = sigma v2 -> v1 = v2.

Lemma EqnBRA_leq_sigma_fin :
  forall x v i j theta theta',
  moveStar (A:=A) (sigma v, theta, i) (sigma x, theta', j) ->
  (x = Vtt \/ Var_omega x = true) ->
  exists ell : nat,
    (i, theta; j, theta', x |= Fpow_emp sigma ell, var v).
Proof.
  unfold Fpow_emp.
  intros x v i j theta theta' H Hf.
  apply moveStar_must_go_forward in H as Hij.
  remember (sigma v, theta, i) as c1 eqn: EQc1.
  remember (sigma x, theta', j) as c2 eqn: EQc2.
  generalize dependent theta;
  generalize dependent i;
  generalize dependent v;
  generalize dependent theta';
  generalize dependent j;
  generalize dependent x.
  induction H as [c1 | c1 c3 c2 Hmov Hstar IH];
  intros x Hf j theta' EQc2 v i Hij theta EQc1.

  - (* When c1 = c2 *)
  rewrite EQc2 in EQc1; clear EQc2.
  inversion EQc1 as [[EQsv EQth EQji]].
  exists 1.
  unfold Fpow.
  apply models_fin_var; auto.
  destruct Hf as [Hf | Hf].
  + (* When x = Vtt *)
  left.
  rewrite Hf.
  rewrite Hf in EQsv;
  rewrite sigma_Vtt in EQsv;
  rewrite <- EQsv.
  apply models_fin_TT; auto.
  + (* When Var_omega x = true *)
  apply sigma_injective_on_Var_omega in EQsv as EQxv;
  auto.
  rewrite <- EQxv.
  right; auto.

  - (* When move c1 c3 /\ moveStar c3 c2 *)
  rewrite EQc1 in Hmov; clear c1 EQc1.
  rewrite EQc2 in Hstar;
  rewrite EQc2 in IH; clear c2 EQc2.
  specialize (IH x Hf j theta' (refl_equal (sigma x, theta', j))).

  destruct c3 as [[q3 th3] i3].
  assert (Hn := Hnormal v).
  remember (sigma v) as sv eqn: EQsv.
  destruct Hn as [v1 v2 | R v1 phi |].

  + (* When sigma v = var v1 .\/ var v2 *)
  inversion_clear Hmov
    as [phi R i1 q1 q2 th Ht|i1 q1 q2 th Ht];
  inversion Ht
    as [|v3 v4 [EQv3 EQv4] EQeps EQnil EQq3
        |v3 v4 [EQv3 EQv4] EQeps EQnil EQq3 |];
  clear v3 EQv3 v4 EQv4 EQeps EQnil;
  rewrite <- EQq3 in Hstar;
  rewrite <- EQq3 in Ht;
  rewrite <- EQq3 in IH;
  clear q3 EQq3;
  apply moveStar_must_go_forward in Hstar as Hi3j.
  * (* When q1 = var v1 .\/ var v2 and q2 = sigma v1 *)
  specialize (IH v1 i3 Hi3j th3
    (refl_equal (sigma v1, th3, i3))).
  destruct IH as [ell IH].
  exists (S ell).
  apply models_fin_var; auto.
  unfold Fpow;
  unfold F;
  left;
  rewrite <- EQsv.
  apply models_fin_OR; auto.
  * (* When q1 = var v1 .\/ var v2 and q2 = sigma v2 *)
  specialize (IH v2 i3 Hi3j th3 (refl_equal (sigma v2, th3, i3))).
  destruct IH as [ell IH].
  exists (S ell).
  apply models_fin_var; auto.
  unfold Fpow;
  unfold F;
  left;
  rewrite <- EQsv.
  apply models_fin_OR; auto.

  + (* When sigma v = ↓ R ,X var v1 ../\ phi *)
  inversion Hmov
    as [phi' R' i1 q1 q2 th Ht Hm [EQq1 EQth EQi1] [EQq2 EQth3 EQi3]
       |i1 q1 q2 th Ht [EQq1 EQth EQi1] [EQq2 EQth3 EQi3]];
    clear q1 EQq1 th EQth i1 EQi1;
    clear q2 EQq2;
  inversion Ht
    as [| | |R2 v2 phi2 [EQR2 EQv2 EQphi2] EQphi' EQR' EQq3];
  clear R2 EQR2 v2 EQv2 phi2 EQphi2.
  rewrite <- EQR' in Ht;
  rewrite <- EQR' in EQth3;
  rewrite <- EQphi' in Ht;
  rewrite <- EQphi' in Hm;
  clear R' EQR' phi' EQphi'.
  rewrite <- EQq3 in Hmov;
  rewrite <- EQq3 in Ht;
  rewrite <- EQq3 in Hstar;
  rewrite <- EQq3 in IH;
  clear q3 EQq3.
  rewrite <- EQi3 in Hmov;
  rewrite <- EQi3 in Hstar;
  rewrite <- EQi3 in IH;
  clear i3 EQi3.
  apply moveStar_must_go_forward in Hstar as HSij.
  specialize (IH v1 (S i) HSij th3 (refl_equal (sigma v1, th3, S i))).
  destruct IH as [ell IH].
  exists (S ell).
  unfold Fpow;
  unfold F.
  apply models_fin_var; auto.
  left.
  rewrite <- EQsv.
  apply models_fin_STORE_X; auto.
  rewrite <- EQth3 in IH.
  apply IH.

  + (* When sigma v = (φ [tt]) *)
  inversion Hmov
    as [phi' R' i1 q1 q2 th Ht Hm [EQq1 EQth EQi1] [EQq2 EQth3 EQi3]
       |i1 q1 q2 th Ht [EQq1 EQth EQi1] [EQq2 EQth3 EQi3]];
  clear q1 EQq1 th EQth i1 EQi1;
  clear q2 EQq2;
  inversion Ht
    as [EQtt EQphi' EQR' EQq3| | |];
  clear EQtt.
  rewrite <- EQR' in Ht;
  rewrite <- EQR' in EQth3;
  rewrite <- EQphi' in Ht;
  rewrite <- EQphi' in Hm;
  clear R' EQR' phi' EQphi'.
  rewrite <- EQq3 in Hmov;
  rewrite <- EQq3 in Ht;
  rewrite <- EQq3 in Hstar;
  rewrite <- EQq3 in IH;
  clear q3 EQq3.
  rewrite <- EQi3 in Hmov;
  rewrite <- EQi3 in Hstar;
  rewrite <- EQi3 in IH;
  clear i3 EQi3.
  rewrite updateR_nil in EQth3.
  rewrite <- EQth3 in Hmov;
  rewrite <- EQth3 in Hstar;
  rewrite <- EQth3 in IH;
  clear th3 EQth3.

  apply tt_loop_keeps_registers in Hstar as Htheta'.
  destruct Htheta' as [EQsx EQtheta'].
  rewrite <- EQtheta'.
  assert (Hx : x = Vtt).
  { destruct Hf as [Hf | Hf]; auto.
    apply sigma_injective_on_Var_omega;
    auto.
    rewrite EQsx.
    now rewrite sigma_Vtt.
  }

  rewrite EQsv in IH.
  apply moveStar_must_go_forward in Hstar as HSij.
  specialize (IH v (S i) HSij theta (refl_equal (sigma v, theta, S i))).
  destruct IH as [ell IH].
  exists (S ell).

  apply models_fin_var; auto.
  unfold Fpow;
  unfold F.
  rewrite <- EQsv.
  rewrite Hx.
  left.
  now apply models_fin_TT.
Qed.


End CorrectnessOfEqnBRA.
