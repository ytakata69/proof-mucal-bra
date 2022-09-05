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

CoInductive acceptingLoop' {A : automaton} : config A -> Prop :=
  acceptingLoop'_intro : forall q1 q2 th1 th2 i j,
    finals A q1 -> finals A q2 ->
    i < j ->
    moveStar (q1, th1, i) (q2, th2, j) ->
    acceptingLoop' (q2, th2, j) ->
    acceptingLoop' (q1, th1, i).

Inductive accepting' {A : automaton} : config A -> Prop :=
  accepting'_intro : forall q1 q2 th1 th2 i j,
    i < j ->
    moveStar (q1, th1, i) (q2, th2, j) ->
    acceptingLoop' (q2, th2, j) ->
    accepting' (q1, th1, i).

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

(* ------------------------------ *)

Section CorrectnessOfEqnBRA.

Variable sigma : eqn_sys.
Let A := EqnBRA sigma.

(* Auxiliaries *)

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
  induction H as [c1 | c1 c3 c2 Hmov Hstar IH];
  intros i theta EQc1.
  - (* When c1 = c2 *)
  split;
  rewrite EQc2 in EQc1;
  now inversion EQc1.
  - (* When move c1 c3 and moveStar c3 c2 *)
  rewrite EQc2 in IH;
  specialize (IH (refl_equal (q, theta', j))).
  rewrite EQc1 in Hmov; clear c1 EQc1.
  destruct c3 as [[q3 th3] i3].
  inversion Hmov
    as [phi R i1 q1 q2 th Ht Hm [EQq1 EQth EQi1] [EQq2 EQth3 EQi3]
       |i1 q1 q2 th Ht [EQq1 EQth EQi1] [EQq2 EQth3 EQi3]];
  clear i1 EQi1 q1 EQq1 q2 EQq2;
  inversion Ht as [EQtt EQphi EQR EQq3| | |];
  clear EQtt.
  rewrite <- EQR in EQth3; clear Ht R EQR.
  rewrite updateR_nil in EQth3.
  rewrite <- EQth3 in IH;
  rewrite <- EQq3 in IH;
  rewrite <- EQi3 in IH.
  specialize (IH (S i) theta (refl_equal (φ [tt], theta, S i)));
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
  generalize dependent th1;
  generalize dependent q1;
  generalize dependent i.
  induction Hm as [| c1 c3 c2 Hmov Hstar IH];
  intros i q1 th1 EQc1.
  - rewrite EQc2 in EQc1.
  inversion EQc1; auto.
  - rewrite EQc2 in IH;
  specialize (IH (refl_equal (q2, th2, j))).
  destruct c3 as [[q3 th3] i3].
  apply le_trans with i3.
  + rewrite EQc1 in Hmov.
  now apply move_must_go_forward with q1 q3 th1 th3.
  + apply IH with q3 th3; auto.
Qed.

Lemma state_is_sigma_v :
  forall v q i j theta theta',
  moveStar (A:=A) (sigma v, theta, i) (q, theta', j) ->
  exists x, q = sigma x.
Proof.
  intros v q i j theta theta' H.
  remember (sigma v, theta, i) as c1 eqn: EQc1.
  remember (q, theta', j) as c2 eqn: EQc2.
  generalize dependent theta;
  generalize dependent i;
  generalize dependent v.
  induction H as [| c1 c3 c2 Hmov Hstar IH];
  intros v i theta EQc1.
  - exists v.
  rewrite EQc2 in EQc1.
  inversion EQc1;
  reflexivity.
  - specialize (IH EQc2).
  rewrite EQc1 in Hmov;
  rewrite EQc2 in Hstar;
  clear c1 EQc1 c2 EQc2.
  destruct c3 as [[q3 th3] i3].
  inversion Hmov
  as [phi R i1 q1 q2 th Ht Hm [EQq1 EQth EQi1] [EQq2 EQth3 EQi3]
     |i1 q1 q2 th Ht [EQq1 EQth EQi1] [EQq2 EQth3 EQi3]].
  + inversion Ht as [EQsv EQphi EQR EQq3| | |R1 v1 p1 EQsv EQphi EQR EQq3].
  * rewrite EQq3 in EQsv.
  rewrite EQsv in IH.
  specialize (IH v i3 th3 (refl_equal (sigma v, th3, i3))).
  apply IH.
  * rewrite <- EQq3 in IH.
  specialize (IH v1 i3 th3 (refl_equal (sigma v1, th3, i3))).
  apply IH.
  + inversion Ht as [| v1 v2 EQsv EQeps EQnil EQq3| v1 v2 EQsv EQeps EQnil EQq3|];
  clear EQeps EQnil;
  rewrite <- EQq3 in IH.
  * specialize (IH v1 i3 th3 (refl_equal (sigma v1, th3, i3))).
  apply IH.
  * specialize (IH v2 i3 th3 (refl_equal (sigma v2, th3, i3))).
  apply IH.
Qed.

Lemma FinalA_tt_Var_omega :
  forall x,
  FinalA sigma (sigma x) <->
  x = Vtt \/ Var_omega x = true.
Proof.
  intro x.
  split; intro H.
  - inversion H as [Hsx|v Hv Hvx].
  + symmetry in Hsx.
  now apply tt_Vtt_or_Var_omega in Hsx.
  + right.
  apply sigma_injective_on_Var_omega with sigma v x in Hv as EQvx;
  auto.
  now rewrite <- EQvx.
  - destruct H as [H | H].
  + rewrite H.
  rewrite sigma_Vtt;
  apply FinalA_TT.
  + now apply FinalA_Var_omega.
Qed.

(* ------------------------------ *)

Hypothesis Hnormal :
  forall v : Var, isNormal (sigma v).

Lemma Fpow_emp_implies_x_tt_Var_omega :
  forall ell x v i j theta theta',
  Fpow_emp sigma ell v i j theta theta' x ->
  x = Vtt \/ Var_omega x = true.
Proof.
  unfold Fpow_emp.
  intros ell x.
  induction ell as [| n IHn];
  intros v i j theta theta' H.
  - (* When ell = 0 *)
  unfold Fpow in H;
  inversion H.
  - (* When ell = S n *)
  inversion H as [Hm | Hm].
  + (* When (i,theta;j,theta',x |= sigma v) *)
  assert (Hn := Hnormal v).
  destruct Hn as [v1 v2 | R v1 phi |].
  * (* When sigma v = var v1 .\/ var v2 *)
  inversion_clear Hm as [| i1 i2 t1 t2 x1 p1 p2 _ Hm' | | |].
  destruct Hm' as [Hm' | Hm'];
  inversion Hm'.
  -- now apply IHn with v1 i j theta theta'.
  -- now apply IHn with v2 i j theta theta'.
  * (* When sigma v = ↓ R ,X var v1 ../\ phi *)
  inversion_clear Hm as [| | i1 i2 t1 t2 x1 R1 p1 p2 Hij Hp Hm'| |];
  inversion Hm';
  now apply IHn with v1 (S i) j (updateR theta R (snd (Str_nth i w))) theta'.
  * (* When sigma v = φ [tt] *)
  inversion Hm;
  left;
  reflexivity.
  + (* When Var_omega v = true /\ x = v *)
  destruct Hm as [Homega [EQxv _]].
  rewrite EQxv; auto.
Qed.

Lemma x_is_either_tt_or_Var_omega :
  forall x v i j theta theta',
  (exists ell : nat,
    (i, theta; j, theta', x |= Fpow_emp sigma ell, var v)) ->
  x = Vtt \/ Var_omega x = true.
Proof.
  intros x v i j theta theta' [ell H].
  apply Fpow_emp_implies_x_tt_Var_omega with ell v i j theta theta'.
  now inversion H.
Qed.

Lemma models_fin_implies_moveStar :
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

Lemma moveStar_implies_models_fin :
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
  generalize dependent v.
  induction H as [c1 | c1 c3 c2 Hmov Hstar IH];
  intros v i Hij theta EQc1.

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
  rewrite EQc2 in IH;
  specialize (IH (refl_equal (sigma x, theta', j))).
  rewrite EQc1 in Hmov; clear c1 EQc1.
  rewrite EQc2 in Hstar; clear c2 EQc2.

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
  apply moveStar_must_go_forward in Hstar as Hi3j;
  [ specialize (IH v1 i3 Hi3j th3 (refl_equal (sigma v1, th3, i3)))
  | specialize (IH v2 i3 Hi3j th3 (refl_equal (sigma v2, th3, i3)))];
  destruct IH as [ell IH];
  exists (S ell);
  apply models_fin_var; auto;
  unfold Fpow;
  unfold F;
  left;
  rewrite <- EQsv;
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
    apply sigma_injective_on_Var_omega with sigma;
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

Theorem models_fin_eq_moveStar :
  forall x v i j theta theta',
  (exists ell : nat,
    (i, theta; j, theta', x |= Fpow_emp sigma ell, var v)) <->
  moveStar (A:=A) (sigma v, theta, i) (sigma x, theta', j) /\
  FinalA sigma (sigma x).
Proof.
  intros x v i j theta theta'.
  split; intro H.
  - split.
  + now apply models_fin_implies_moveStar.
  + apply FinalA_tt_Var_omega.
  now apply x_is_either_tt_or_Var_omega with v i j theta theta'.
  - destruct H as [H1 H2].
  apply FinalA_tt_Var_omega in H2.
  now apply moveStar_implies_models_fin.
Qed.

Lemma models_fin_ell_implies_moveStar :
  forall ell x v i j theta theta',
  (i, theta; j, theta', x |= Fpow_emp sigma ell, var v) ->
  moveStar (A:=A) (sigma v, theta, i) (sigma x, theta', j) /\
  FinalA sigma (sigma x).
Proof.
  intros ell x v i j theta theta' H.
  split.
  + apply models_fin_implies_moveStar;
  now exists ell.
  + apply FinalA_tt_Var_omega.
  apply x_is_either_tt_or_Var_omega with v i j theta theta';
  now exists ell.
Qed.

(* ------------------------------ *)

Lemma acceptingLoop_implies_sigma :
  forall v i theta,
  acceptingLoop (A:=A) (sigma v, theta, i) ->
  (i, theta |= lfpF, var v).
Proof.
  cofix Hcofix.
  intros v i theta H.
  inversion H as [q th1 th2 i1 j Hf Hij Hstar Ha [EQqc1 EQth1 EQi1]].
  apply moveStar_implies_models_fin in Hstar as Hm1.
  - destruct Hm1 as [ell Hm1].
  inversion_clear Hm1 as [i2 j1 th3 th4 x v1 Hij' HF | | | |].
  apply models_var with j th2 v; try assumption.
  + now apply lfpF_is_upperbound with sigma ell.
  + now apply Hcofix.
  - now apply FinalA_tt_Var_omega.
Qed.

Theorem accepting_implies_sigma :
  forall v i theta,
  accepting (A:=A) (sigma v, theta, i) ->
  (i, theta |= lfpF, var v).
Proof.
  intros v i theta H.
  inversion H
  as [q1 q2 th1 th2 i1 j Hij Hstar Ha [EQq1 EQth1 EQi1]];
  clear q1 EQq1 th1 EQth1 i1 EQi1.
  apply state_is_sigma_v in Hstar as Hsx.
  destruct Hsx as [x Hsx].
  rewrite Hsx in Ha;
  rewrite Hsx in Hstar;
  clear q2 Hsx.
  apply acceptingLoop_implies_sigma in Ha as Ha'.
  apply models_var with j th2 x; try assumption.
  apply moveStar_implies_models_fin in Hstar.
  - destruct Hstar as [ell Hstar].
  apply lfpF_is_upperbound with sigma ell.
  inversion Hstar;
  assumption.
  - apply FinalA_tt_Var_omega.
  now inversion Ha.
Qed.

Lemma sigma_implies_acceptingLoop' :
  forall v i theta,
  (i, theta |= lfpF, var v) ->
  (v = Vtt \/ Var_omega v = true) ->
  acceptingLoop' (A:=A) (sigma v, theta, i).
Proof.
  cofix Hcofix.
  intros v i theta H Hf.
  inversion H as [i1 j th1 th2 x v1 HF Hij Hchain EQi1 EQth1 EQv1 | | |];
  clear i1 EQi1 th1 EQth1 v1 EQv1.
  apply lfpF_is_sup with sigma v i j theta th2 x in HF;
  destruct HF as [ell HF].
  apply Fpow_emp_implies_x_tt_Var_omega in HF as Hfx;
  apply FinalA_tt_Var_omega in Hfx as Hfx'.

  assert (Hf' : FinalA sigma (sigma v)).
  { apply FinalA_tt_Var_omega; auto. }
  apply (acceptingLoop'_intro (A:=A)) with (q2:=sigma x) (th2:=th2) (j:=j);
  try assumption.
  - apply models_fin_implies_moveStar.
  exists ell.
  apply models_fin_var; try assumption.
  now apply Nat.lt_le_incl.
  - apply Hcofix; try assumption.
Qed.

Theorem sigma_implies_accepting' :
  forall v i theta,
  (i, theta |= lfpF, var v) ->
  accepting' (A:=A) (sigma v, theta, i).
Proof.
  intros v i theta H.
  inversion H as [i1 j th1 th2 x v1 HF Hij Hm EQi1 EQth1 EQv1| | |];
  clear th1 EQth1 i1 EQi1 v1 EQv1.
  apply lfpF_is_sup with sigma v i j theta th2 x in HF;
  destruct HF as [ell HF].
  apply (accepting'_intro (A:=A) (sigma v) (sigma x) theta th2 i j);
  try assumption.
  - apply models_fin_implies_moveStar.
  exists ell.
  apply models_fin_var; auto.
  now apply Nat.lt_le_incl.
  - apply sigma_implies_acceptingLoop'; auto.
  now apply Fpow_emp_implies_x_tt_Var_omega in HF.
Qed.

End CorrectnessOfEqnBRA.
