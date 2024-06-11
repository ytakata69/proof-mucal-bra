(*
 * mu-calculus for infinite data words:
 * Basic definition of LTL.
 *)

Require Export Nat Arith.
Require Export Lists.List.
Require Export Lists.Streams.
Require Import Sets.Ensembles.

(* data words *)
 
Definition D := nat.
Definition At := nat.
Definition Sigma := At -> bool.
Definition data_word := Stream (Sigma * D)%type.
 
(* LTL syntax *)
 
Definition register := nat.
Definition Var := nat.

Inductive ltl_atom :=
  | tt : ltl_atom
  | MATCH : register -> ltl_atom
  | p : At -> ltl_atom  (* an atomic proposition *)
  .
Inductive ltl_phi :=
  | pos : ltl_atom -> ltl_phi  (* a positive literal *)
  | neg : ltl_atom -> ltl_phi  (* a negative literal *)
  | AND_phi : ltl_phi -> ltl_phi -> ltl_phi
  .
Inductive ltl :=
  | var : Var -> ltl
  | OR  : ltl -> ltl -> ltl
  | STORE_X : (list register) -> ltl -> ltl_phi -> ltl
  | PHI : ltl_phi -> ltl
  .

Notation "'↑' r" := (MATCH r) (at level 75).
Notation "a '.\/' b" := (OR   a b) (at level 85, right associativity).
Notation "a './\' b" := (AND_phi a b) (at level 75, right associativity).
Notation  "'[' a ']'" := (pos a).
Notation "'~[' a ']'" := (neg a).
Notation "'φ' p" := (PHI p) (at level 78).
Notation "'↓' R ',X' psi '../\' phi" := (STORE_X R psi phi) (at level 200).

(*
Check (STORE_X (1 :: nil) (OR (PHI (neg (p 1))) (PHI (pos (p 2)))) (pos (↑ 1))).
Check (↓ (1 :: nil) ,X ((φ ~[p 1]) .\/ (φ [p 2])) ../\ [↑1]).
*)

(* LTL semantics *)

Definition Theta := register -> D.

Definition update
  (theta : Theta) (i : register) (d : D) : Theta :=
  fun (r : register) =>
    if r =? i then d else theta r.
Fixpoint updateR
  (theta : Theta) (R : list register) (d : D) : Theta :=
  match R with
  | h :: t => update (updateR theta t d) h d
  | nil => theta
  end.

Definition theta_bot : Theta :=
  fun (r : register) => 0.

Definition Vtt : Var := 0.

(* Input data word : Env and models are depends on w *)
Parameter w : data_word.
Definition Env := Var -> nat -> nat -> Theta -> Theta -> Var -> Prop.

Definition empty_env : Env :=
  fun (v : Var) (i j : nat) (theta theta' : Theta) (x : Var)
    => False.

Definition models_atom
  (i : nat) (theta : Theta) (atom : ltl_atom)
  : Prop :=
  match atom with
  | tt => True
  | p a => fst (Str_nth i w) a = true
  | ↑ r => snd (Str_nth i w) = theta r
  end.

Inductive models_phi
  (i : nat) (theta : Theta) : ltl_phi -> Prop :=
  | models_pos : forall atom : ltl_atom,
    models_atom i theta atom -> models_phi i theta (pos atom)
  | models_neg : forall atom : ltl_atom,
    ~models_atom i theta atom -> models_phi i theta (neg atom)
  | models_AND_phi : forall (p1 p2 : ltl_phi),
    models_phi i theta p1 -> models_phi i theta p2
    -> models_phi i theta (AND_phi p1 p2)
  .

CoInductive models (u : Env)
  : nat -> Theta -> ltl -> Prop :=
  | models_var : forall i j theta theta' x v,
      u v i j theta theta' x ->
      i < j ->
      models u j theta' (var x) ->
      models u i theta (var v)
  (*
  | models_OR : forall i theta psi1 psi2,
      models u i theta psi1 \/
      models u i theta psi2 ->
      models u i theta (OR psi1 psi2)
  | models_STORE_X : forall i theta R psi phi,
      models_phi i theta phi ->
      models u (S i) (updateR theta R (snd (Str_nth i w))) psi ->
      models u i theta (↓ R ,X psi ../\ phi)
  | models_PHI : forall i theta phi,
      models_phi i theta phi ->
      models u i theta (φ phi)
  *)
  .

Notation "'(' i ',' theta '|=' u ',' psi ')'"
  := (models u i theta psi).

(* Equality of two assignments *)

Axiom Theta_extensionality :
  forall theta1 theta2 : Theta,
    (forall r, theta1 r = theta2 r) -> theta1 = theta2.

Lemma updateR_nil :
  forall theta d,
  updateR theta nil d = theta.
Proof.
  intros theta d.
  apply Theta_extensionality.
  intro r.
  now unfold updateR.
Qed.

(* Semantics on finite sequences *)

Inductive models_fin (u : Env)
  : nat -> nat -> Theta -> Theta -> Var -> ltl -> Prop :=
  | models_fin_var : forall i j theta theta' x v,
      i <= j ->
      u v i j theta theta' x ->
      models_fin u i j theta theta' x (var v)
  | models_fin_OR : forall i j theta theta' x psi1 psi2,
      i <= j ->
      models_fin u i j theta theta' x psi1 \/
      models_fin u i j theta theta' x psi2 ->
      models_fin u i j theta theta' x (OR psi1 psi2)
  | models_fin_STORE_X : forall i j theta theta' x R psi phi,
      i < j ->
      models_phi i theta phi ->
      models_fin u (S i) j (updateR theta R (snd (Str_nth i w))) theta' x psi ->
      models_fin u i j theta theta' x (↓ R ,X psi ../\ phi)
  | models_fin_TT : forall i j theta,
      i <= j ->
      models_fin u i j theta theta Vtt (φ [tt])
  | models_fin_PHI : forall i j theta (phi : ltl_phi),
      phi <> [tt] ->
      i < j ->
      models_phi i theta phi ->
      models_fin u i j theta theta Vtt (φ phi)
  .

Notation "'(' i ',' theta ';' j ',' theta' ',' x '|=' u ',' psi ')'"
  := (models_fin u i j theta theta' x psi).

(* Equation systems *)

Definition eqn_sys := Var -> ltl.  (* the type of equation systems *)

Parameter Var_omega : Var -> Prop.

(* The transformation from Env to Env *)
Definition F (sigma : eqn_sys) (u : Env) : Env :=
  fun (v : Var) (i j : nat) (theta theta' : Theta) (x : Var) =>
  (i, theta; j, theta', x |= u, sigma v)
  \/ (Var_omega v /\ x = v /\ i = j /\ theta = theta').

(* power of F *)
Fixpoint Fpow (sigma : eqn_sys) (i : nat) (u : Env) : Env :=
  match i with
    0   => u
  | S n => F sigma (Fpow sigma n u)
  end.
Definition Fpow_emp sigma i := Fpow sigma i empty_env.


(* Continuities *)

Section Continuities.

Definition env_leq (u1 u2 : Env) : Prop :=
  forall v : Var,
  forall i j theta theta' x,
  u1 v i j theta theta' x -> u2 v i j theta theta' x.

Inductive env_union : Ensemble Env -> Env :=
  env_union_intro :
    forall (s : Ensemble Env) u,
      In Env s u ->
    forall v i j theta theta' x,
      u v i j theta theta' x ->
      env_union s v i j theta theta' x.

Inductive Ens_map {A : Type} : (A -> A) -> Ensemble A -> Ensemble A :=
  Ens_map_intro :
    forall (f : A -> A) (s : Ensemble A) (u : A),
    In A s u -> In A (Ens_map f s) (f u).

Lemma env_leq_union :
  forall (s : Ensemble Env) (u : Env),
    In Env s u -> env_leq u (env_union s).
Proof.
  intros s u Hin.
  unfold env_leq;
  intros v i j theta theta' x Hu.
  now apply env_union_intro with u.
Qed.


Lemma models_fin_is_monotonic :
  forall (u1 u2 : Env),
    env_leq u1 u2 ->
  forall psi i j theta theta' x,
    (i, theta; j, theta', x |= u1, psi) ->
    (i, theta; j, theta', x |= u2, psi).
Proof.
  intros u1 u2 Hu1u2 psi.
  induction psi
  as [| psi1 IH1 psi2 IH2
      | R psi IH phi
      | phi ];
  intros i j theta theta' x H.
  - (* When psi = var v *)
  inversion H;
  apply models_fin_var; auto.
  - (* When psi = l1 .\/ l2 *)
  inversion_clear H as [|i1 j1 t1 t2 x1 p1 p2 Hij Hor| | |];
  apply models_fin_OR; auto;
  destruct Hor as [Hor | Hor];
  [left | right];
  [apply IH1 | apply IH2];
  auto.
  - (* When psi = ↓ R ,X psi ../\ phi *)
  inversion H;
  apply models_fin_STORE_X; auto.
  - (* When psi = φ phi *)
  inversion H.
  + now apply models_fin_TT.
  + now apply models_fin_PHI.
Qed.

Lemma models_fin_is_continuous_half :
  forall (s : Ensemble Env),
    (exists u, In Env s u) (* non-empty *) ->
  forall psi i j theta theta' x,
    (i, theta; j, theta', x |= env_union s, psi) ->
  exists u, In Env s u /\
    (i, theta; j, theta', x |= u, psi).
Proof.
  intros s Hnonemp psi.
  induction psi
  as [v | psi1 IH1 psi2 IH2 | R psi IH phi | phi];
  intros i j theta theta' x H.
  - (* When psi = var v *)
  inversion_clear H as [i1 j1 t1 t2 x1 v2 Hij Huni| | | |].
  inversion_clear Huni as [s1 u].
  exists u.
  split; auto.
  apply models_fin_var; auto.
  - (* When psi = psi1 .\/ psi2 *)
  inversion_clear H as [|i1 j1 t1 t2 x1 p1 p2 Hij Huni| | |].
  destruct Huni as [Huni | Huni];
  [apply IH1 in Huni | apply IH2 in Huni];
  destruct Huni as [u [Hin Huni]];
  exists u;
  split; auto;
  apply models_fin_OR; auto.
  - (* When psi = ↓ R ,X psi ../\ phi *)
  inversion_clear H as [| |i1 j1 t1 t2 x1 R1 p1 p2 Hij Hm Huni| |].
  apply IH in Huni.
  destruct Huni as [u [Hin Huni]].
  exists u.
  split; auto.
  apply models_fin_STORE_X; auto.
  - (* When psi = (φ phi) *)
  destruct Hnonemp as [u Hin].
  exists u;
  split; auto.
  inversion H as [| | | i1 j1 t1 Hij |].
  + now apply models_fin_TT.
  + now apply models_fin_PHI.
Qed.

Theorem models_fin_is_continuous :
  forall (s : Ensemble Env),
    (exists u, In Env s u) (* non-empty *) ->
  forall psi i j theta theta' x,
    (i, theta; j, theta', x |= env_union s, psi) <->
    (exists u, In Env s u /\
      (i, theta; j, theta', x |= u, psi)).
Proof.
  intros s Hnonemp psi i j theta theta' x.
  split.
  - (* -> *)
  now apply models_fin_is_continuous_half.
  - (* <- *)
  intros [u [Hin Hm]].
  apply models_fin_is_monotonic with u; auto.
  now apply env_leq_union.
Qed.


Variable sigma : eqn_sys.

Lemma F_is_monotonic :
  forall (u1 u2 : Env),
    env_leq u1 u2 ->
    env_leq (F sigma u1) (F sigma u2).
Proof.
  intros u1 u2 Hu1u2.
  unfold env_leq.
  intros v i j theta theta' x.
  unfold F.
  intro H;
  destruct H as [H | H].
  - left;
  now apply models_fin_is_monotonic with u1.
  - now right.
Qed.

Lemma F_is_continuous_1st_half :
  forall (s : Ensemble Env),
    (exists u, In Env s u) (* non-empty *) ->
    env_leq (F sigma (env_union s)) (env_union (Ens_map (F sigma) s)).
Proof.
  intros s Hnonemp.
  unfold env_leq.
  intros v i j theta theta' x H.
  inversion H as [Hm | Hf].
  - (* When (i,theta;j,theta',x |= sigma v) *)
  apply models_fin_is_continuous in Hm; auto.
  destruct Hm as [u [Hin Hm]].
  apply env_union_intro with (F sigma u).
  + now apply Ens_map_intro.
  + unfold F;
  now left.
  - (* When Var_omega v *)
  destruct Hnonemp as [u Hin].
  apply env_union_intro with (F sigma u).
  + now apply Ens_map_intro.
  + unfold F;
  now right.
Qed.

Lemma F_is_continuous_2nd_half :
  forall (s : Ensemble Env),
    (exists u, In Env s u) (* non-empty *) ->
    env_leq (env_union (Ens_map (F sigma) s)) (F sigma (env_union s)).
Proof.
  intros s Hnonemp.
  unfold env_leq.
  intros v i j theta theta' x H.
  inversion_clear H as [s1 u Hin v1 i1 j1 t1 t2 x1 Hu].
  inversion Hin as [f s1 u1 Hin1 EQf EQs1 EQu1].
  rewrite <- EQu1 in Hu.
  unfold F;
  unfold F in Hu.
  destruct Hu as [Hu | Hu]; [left | right]; auto.
  apply models_fin_is_monotonic with u1;
  auto.
  now apply env_leq_union.
Qed.

Theorem F_is_continuous :
  forall (s : Ensemble Env),
    (exists u, In Env s u) (* non-empty *) ->
    env_leq (F sigma (env_union s)) (env_union (Ens_map (F sigma) s)) /\
    env_leq (env_union (Ens_map (F sigma) s)) (F sigma (env_union s)).
Proof.
  intros s Hnonemp.
  split.
  - now apply F_is_continuous_1st_half.
  - now apply F_is_continuous_2nd_half.
Qed.

End Continuities.

Section LeastFixedPoint.

Variable sigma : eqn_sys.

Inductive all_Fpow : Ensemble Env :=
  all_Fpow_intro :
    forall ell : nat, In Env all_Fpow (Fpow_emp sigma ell).

Definition lfpF : Env := env_union all_Fpow.

Lemma lfpF_is_upperbound_Fpow :
  forall ell v i j theta theta' x,
  Fpow_emp sigma ell v i j theta theta' x ->
  lfpF v i j theta theta' x.
Proof.
  intros ell v i j theta theta' x H.
  unfold lfpF.
  apply env_union_intro with (Fpow_emp sigma ell); auto.
  apply all_Fpow_intro.
Qed.

Theorem lfpF_is_sup_Fpow :
  forall v i j theta theta' x,
  lfpF v i j theta theta' x <->
  exists ell,
  Fpow_emp sigma ell v i j theta theta' x.
Proof.
  intros v i j theta theta' x.
  split; intro H.
  - (* -> *)
  unfold lfpF in H.
  inversion_clear H as [s u Hin v1 i1 j1 t1 t2 x1 Hu].
  inversion Hin as [ell EQu].
  exists ell.
  now rewrite EQu.
  - (* <- *)
  destruct H as [ell H].
  now apply lfpF_is_upperbound_Fpow with ell.
Qed.

End LeastFixedPoint.

(* Syntactical assumptions *)

(* The meaning of Vtt *)
Axiom sigma_Vtt : forall sigma : eqn_sys,
  sigma Vtt = (φ [tt]).

Axiom Vtt_is_Var_omega :
  Var_omega Vtt.

Axiom sigma_injective_on_Var_omega :
  forall (sigma : eqn_sys) (v1 v2 : Var),
  Var_omega v1 ->
  sigma v1 = sigma v2 -> v1 = v2.

Section SyntacticalProperties.

Variable sigma : eqn_sys.

Lemma models_fin_implies_x_Var_omega :
  forall ell x psi i j theta theta',
  (i, theta; j, theta', x |= Fpow_emp sigma ell, psi) ->
  Var_omega x.
Proof.
  unfold Fpow_emp.
  intros ell x.
  induction ell as [| n IHn];
    intros psi i j theta theta' H.
  - (* base case (ell = 0) *)
    generalize dependent i.
    generalize dependent theta.
    induction psi as [v | psi1 IH1 psi2 IH2
      | R psi1 IH phi | phi];
      intros theta i H.
    + (* when psi = var v *)
      inversion_clear H as [i' j' th th' x' v' Hij H'
        | | | |].
      inversion H'.
    + (* when psi = psi1 .\/ psi2 *)
      inversion_clear H as [| i' j' th th' x' p1 p2 Hij H'
        | | |].
      destruct H' as [H' | H'];
        [ apply IH1 with theta i
        | apply IH2 with theta i];
        auto.
    + (* when psi = ↓ R,X psi1 ../\ phi *)
      inversion_clear H as [|
        | i' j' th th' x' v psi1' phi' Hij Hm' H' | |].
      now apply IH with (updateR theta R (snd (Str_nth i w))) (S i).
    + (* when psi = φ phi *)
      inversion H;
      apply Vtt_is_Var_omega.
  - (* inductive step (ell = S n) *)
    generalize dependent i.
    generalize dependent theta.
    induction psi as [v | psi1 IH1 psi2 IH2
      | R psi1 IH phi | phi];
      intros theta i H.
    + (* when psi = var v *)
      inversion_clear H as [i' j' th th' x' v' Hij H'
        | | | |].
      inversion H' as [H | Hf].
      * now apply IHn with (sigma v) i j theta theta'.
      * destruct Hf as [Hvo [EQxv _]].
        now rewrite EQxv.
    + (* when psi = psi1 .\/ psi2 *)
      inversion_clear H as [| i' j' th th' x' p1 p2 Hij H'
        | | |].
      destruct H' as [H' | H'];
        [ apply IH1 with theta i
        | apply IH2 with theta i];
        auto.
    + (* when psi = ↓ R,X psi1 ../\ phi *)
      inversion_clear H as [|
        | i' j' th th' x' v psi1' phi' Hij Hm' H' | |].
      now apply IH with (updateR theta R (snd (Str_nth i w))) (S i).
    + (* when psi = φ phi *)
      inversion H;
      apply Vtt_is_Var_omega.
Qed.

Lemma Fpow_emp_implies_x_Var_omega :
  forall ell x v i j theta theta',
  Fpow_emp sigma ell v i j theta theta' x ->
  Var_omega x.
Proof.
  unfold Fpow_emp.
  intros ell x.
  induction ell as [| n IHn];
    intros v i j theta theta' H.
  - (* base case (ell = 0) *)
    unfold Fpow in H;
    inversion H.
  - (* inductive step (ell = S n) *)
    inversion H as [Hm | Hm].
    + (* when (i,theta;j,theta',x |= sigma v) *)
      now apply models_fin_implies_x_Var_omega
        with n (sigma v) i j theta theta'.
    + (* When Var_omega v /\ x = v *)
      destruct Hm as [Homega [EQxv _]].
      now rewrite EQxv.
Qed.

Lemma x_is_Var_omega :
  forall x v i j theta theta',
  (exists ell : nat,
    (i, theta; j, theta', x |= Fpow_emp sigma ell, var v)) ->
  Var_omega x.
Proof.
  intros x v i j theta theta' [ell H].
  apply Fpow_emp_implies_x_Var_omega with ell v i j theta theta'.
  now inversion H.
Qed.

End SyntacticalProperties.

(* Equality of two ltl formulas *)

Section LTL_equality.

Variable sigma : eqn_sys.
Variable ell : nat.
Hypothesis Hell : ell >= 1.
Let u := Fpow_emp sigma ell.

Lemma Hell' :
  exists ell', ell = S ell'.
Proof.
  destruct ell as [| ell'].
  - unfold ge in Hell.
    now apply Nat.nle_succ_0 in Hell.
  - now exists ell'.
Qed.

(* Vtt can be seen as the same as tt *)
Lemma always_models_Vtt :
  forall i theta,
    (i, theta |= u, var Vtt).
Proof.
  intros i theta.
  generalize dependent i.
  cofix Hcofix.
  intros i.
  apply models_var with (j:=S i) (theta':=theta) (x:=Vtt).
  - destruct Hell' as [ell' Hell'].
    unfold u, Fpow_emp, Fpow.
    rewrite Hell'.
    left.
    rewrite sigma_Vtt.
    apply models_fin_TT.
    apply Nat.le_succ_diag_r.
  - apply Nat.lt_succ_diag_r.
  - apply Hcofix.
Qed.

Lemma tt_eq_Vtt :
  forall i theta,
    models_phi i theta [tt]
    <-> (i, theta |= u, var Vtt).
Proof.
  intros i theta.
  split.
  - (* -> *)
    intros H.
    now apply always_models_Vtt.
  - (* <- *)
    intros H.
    apply models_pos.
    now unfold models_atom.
Qed.

Lemma phi_eq_xtt_phi :
  forall phi : ltl_phi,
  forall Vphi,
    sigma Vphi = (↓ nil ,X (φ [tt]) ../\ phi) ->
  forall i theta,
    models_phi i theta phi
    <-> (i, theta |= u, var Vphi).
Proof.
  intros phi Vphi EQvp.
  intros i theta.
  destruct Hell' as [ell' Hell'].
  split; intro H.
  - (* phi -> Xtt ../\ phi *)
    unfold u, Fpow_emp, Fpow.
    rewrite Hell'.
    apply models_var with (j:=S i) (theta':=theta) (x:=Vtt).
    + left.
      rewrite EQvp.
      apply models_fin_STORE_X.
      * apply Nat.lt_succ_diag_r.
      * apply H.
      * rewrite updateR_nil.
        now apply models_fin_TT.
    + apply Nat.lt_succ_diag_r.
    + assert (Htt := always_models_Vtt).
      specialize (Htt (S i) theta).
      unfold u, Fpow_emp in Htt.
      rewrite Hell' in Htt.
      unfold Fpow in Htt.
      apply Htt.
  - (* Xtt ../\ phi -> phi *)
    inversion H as
      [i1 j th1 th2 x y Hu Hij Hx EQi1 EQth1 EQy];
    clear i1 EQi1 th1 EQth1 y EQy.
    unfold u, Fpow_emp in Hu.
    rewrite Hell' in Hu.
    unfold Fpow, F in Hu.
    destruct Hu as [Hu | Hu].
    + (* when (i, theta; j, th2, x |= sigma Vphi) *)
      rewrite EQvp in Hu.
      now inversion Hu.
    + (* when x = Vphi /\ (i,theta) = (j,th2) *)
      destruct Hu as [_ [_ [EQij _]]].
      rewrite EQij in Hij.
      now apply Nat.lt_irrefl in Hij.
Qed.

Lemma psi_eq_psi_or_ff :
  forall psi : ltl,
  forall V1 V2,
    sigma V1 = psi ->
    sigma V2 = (psi .\/ (φ ~[tt])) ->
    (Var_omega V1 <-> Var_omega V2) ->
  forall i theta,
    (i, theta |= u, var V1)
    <-> (i, theta |= u, var V2).
Proof.
  intros psi V1 V2 EQv1 EQv2 Hvo i theta.
  destruct Hell' as [ell' Hell'].
  unfold u, Fpow_emp.
  rewrite Hell'.

  split; intro H.
  - (* psi -> psi .\/ ff *)
    generalize dependent theta.
    generalize dependent i.
    cofix Hcofix.

    intros i theta H.
    inversion H as
      [i1 j th1 th2 x y Hu Hij Hx EQi1 EQth1 EQy];
    clear i1 EQi1 th1 EQth1 y EQy.
    unfold Fpow, F in Hu.
    destruct Hu as [Hu | Hu].
    + apply models_var with (j:=j) (theta':=th2) (x:=x);
      auto.
      unfold Fpow, F.
      rewrite EQv1 in Hu.
      rewrite EQv2.
      left.
      apply models_fin_OR.
      * now apply Nat.lt_le_incl.
      * now left.
    + destruct Hu as [Ho1 [EQx [EQij EQtheta]]].
      apply models_var with (j:=j) (theta':=th2) (x:=V2);
      auto.
      * rewrite EQij, EQtheta.
        apply Hvo in Ho1.
        unfold Fpow, F.
        now right.
      * rewrite EQx in Hx.
        now apply Hcofix.
  - (* psi .\/ ff -> psi *)
    generalize dependent theta.
    generalize dependent i.
    cofix Hcofix.

    intros i theta H.
    inversion H as
      [i1 j th1 th2 x y Hu Hij Hx EQi1 EQth1 EQy];
    clear i1 EQi1 th1 EQth1 y EQy.
    unfold Fpow, F in Hu.
    destruct Hu as [Hu | Hu].
    + apply models_var with (j:=j) (theta':=th2) (x:=x);
      auto.
      unfold Fpow, F.
      rewrite EQv2 in Hu.
      rewrite EQv1.
      left.
      inversion Hu as [
        | i' j' th1' th2' x' p1' p2' Hij' Hu'
          EQi' EQj' EQth1' EQth2' EQx' [EQp1' EQp2'] | | |];
      clear i' EQi' j' EQj' th1' EQth1' th2' EQth2'
            x' EQx' p1' EQp1' p2' EQp2'
            Hu Hij'.
      destruct Hu' as [Hu | Hu]; auto.
      inversion Hu as [| | |
        | i' j' th1' p1' Htt Hij' Hmo
          EQi' EQj' EQth1' EQth2 EQx EQp1'];
      clear i' EQi' j' EQj' th1' EQth1' p1' EQp1'
            Htt.
      inversion Hmo as [| a Hmo' EQa |];
      clear a EQa.
      assert (Htt : models_atom i th2 tt).
      { now unfold models_atom. }
      now apply Hmo' in Htt.
    + destruct Hu as [Ho2 [EQx [EQij EQtheta]]].
      apply models_var with (j:=j) (theta':=th2) (x:=V1);
      auto.
      * rewrite EQij, EQtheta.
        apply Hvo in Ho2.
        unfold Fpow, F.
        now right.
      * rewrite EQx in Hx.
        now apply Hcofix.
Qed.

End LTL_equality.

Section NormalForms.
Definition Var_eq_dec := Nat.eq_dec.

Theorem Fpow_is_monotonic :
  forall (sigma : eqn_sys) (i : nat),
  env_leq (Fpow_emp sigma i) (Fpow_emp sigma (S i)).
Proof.
  intros sigma i.
  induction i as [| i IH].
  - (* base case *)
    intros v i j theta theta' x H.
    now unfold Fpow_emp, Fpow, empty_env in H.
  - (* inductive step *)
    unfold Fpow_emp, Fpow.
    now apply F_is_monotonic.
Qed.

(* Normalized LTL formulas *)

Inductive isNormal : ltl -> Prop :=
  | isNormal_OR : forall v v' : Var,
      isNormal (var v .\/ var v')
  | isNormal_STORE_X :
      forall R (v : Var) (phi : ltl_phi),
      isNormal (↓ R ,X (var v) ../\ phi)
  | isNormal_TT :
      isNormal (φ [tt])
  .

Definition env_eq (e1 e2 : Env) :=
  env_leq e1 e2 /\ env_leq e2 e1.

Section NormalizeOr.

Variables sigma1 sigma2 : eqn_sys.
Variables v1 v2 v3 : Var.
Hypothesis sigma_equiv :
  forall v, v <> v3 -> sigma1 v = sigma2 v.
Hypothesis v1_neq_v3 : v1 <> v3.
Hypothesis v2_neq_v3 : v2 <> v3.
Hypothesis EQv3_1 : sigma1 v3 = ((sigma1 v1) .\/ (sigma1 v2)).
Hypothesis EQv3_2 : sigma2 v3 = ((var v1) .\/ (var v2)).
Hypothesis v1_not_Var_omega : ~ Var_omega v1.
Hypothesis v2_not_Var_omega : ~ Var_omega v2.

Lemma normalize_or_1 :
  forall l,
  env_leq (Fpow_emp sigma2 l) (Fpow_emp sigma1 l).
Proof.
  induction l as [| l IHl].
  - (* base case *)
    unfold Fpow_emp, Fpow.
    now unfold env_leq.
  - (* inductive step *)
    unfold env_leq.
    intros v i j theta theta' x.
    unfold Fpow_emp, Fpow, F.
    intros H.
    destruct H as [H | H];
      [left | (right; apply H)].
    destruct (Var_eq_dec v v3)
      as [v_eq_v3 | v_neq_v3].
    + (* when v = v3 *)
      rewrite v_eq_v3, EQv3_1.
      rewrite v_eq_v3, EQv3_2 in H; clear v v_eq_v3.
      inversion H as [|
        i' j' th th' x' p1 p2 Hij Ho
        EQi' EQj' EQth EQth' EQx' [EQp1 EQp2] | | |];
        clear i' EQi' j' EQj' th EQth th' EQth' x' EQx'
              p1 EQp1 p2 EQp2 H.
      (* Ho: ... |= var v1 \/ ... |= var v2 *)
      destruct Ho as [Ho | Ho];
        apply models_fin_OR; auto;
        [left | right];
        inversion Ho as
          [i' j' th th' x' v' Hij' Hf
            EQi' EQj' EQth EQth' EQx' EQv' | | | |];
        clear i' EQi' j' EQj' th EQth th' EQth' x' EQx'
              v' EQv' Hij' Ho;
        apply IHl in Hf;
        apply Fpow_is_monotonic in Hf;
        unfold Fpow_emp, Fpow, F in Hf;
        destruct Hf as [Hf | [v12_omega _]];
        try apply Hf.
        * now apply v1_not_Var_omega in v12_omega.
        * now apply v2_not_Var_omega in v12_omega.
    + (* when v <> v3 *)
      rewrite (sigma_equiv _ v_neq_v3).
      apply (models_fin_is_monotonic _ _ IHl).
      apply H.
Qed.

Lemma normalize_or_2 :
  forall l,
  env_leq (Fpow_emp sigma1 l) (Fpow_emp sigma2 (2 * l)).
Proof.
  intros l.
  simpl.
  rewrite <- (plus_n_O l).
  induction l as [| l IHl].
  - (* base case *)
    unfold Fpow_emp, Fpow.
    now unfold env_leq.
  - (* inductive step *)
    simpl.
    unfold env_leq.
    rewrite <- (plus_n_Sm l l).
    intros v i j th th' x.
    destruct (Var_eq_dec v v3)
      as [v_eq_v3 | v_neq_v3].
    + (* when v = v3 *)
      rewrite v_eq_v3;
        clear v v_eq_v3.
      unfold Fpow_emp, Fpow, F.
      intros H.
      destruct H as [H | H];
        [left | (right; apply H)].

      (* when ... |= sigma1 v1 .\/ sigma1 v2 *)
      rewrite EQv3_2.
      rewrite EQv3_1 in H.
      inversion H as [
        | i' j' th1 th2 x' p1 p2 Hij Ho
          EQi' EQj' EQth1 EQth2 EQx' [EQp1 EQp2]
        | | |];
        clear i' EQi' j' EQj' th1 EQth1 th2 EQth2
              x' EQx' p1 EQp1 p2 EQp2 H.
      apply models_fin_OR; auto.
      destruct Ho as [Ho | Ho];
        [left | right];
        apply (models_fin_is_monotonic _ _ IHl) in Ho;
        apply models_fin_var; auto;
        unfold F;
        left.
      * now rewrite (sigma_equiv _ v1_neq_v3) in Ho.
      * now rewrite (sigma_equiv _ v2_neq_v3) in Ho.
    + (* when v <> v3 *)
      unfold Fpow_emp, Fpow, F.
      rewrite <- (sigma_equiv _ v_neq_v3).
      intros H.
      destruct H as [H | H];
        [left | (right; apply H)].
      apply (models_fin_is_monotonic _ _ IHl) in H.
      apply (models_fin_is_monotonic _ _
        (Fpow_is_monotonic sigma2 (l + l))).
      apply H.
Qed.

Theorem normalize_or :
  env_eq (lfpF sigma1) (lfpF sigma2).
Proof.
  unfold env_eq.
  split;
  unfold env_leq;
  intros v i j th th' x;
  rewrite lfpF_is_sup_Fpow;
  rewrite lfpF_is_sup_Fpow;
  intros [l H].
  - exists (2 * l).
    now apply normalize_or_2.
  - exists l.
    now apply normalize_or_1.
Qed.

End NormalizeOr.

Section NormalizeStoreX.

Variables sigma1 sigma2 : eqn_sys.
Variables v1 v3 : Var.
Hypothesis sigma_equiv :
  forall v, v <> v3 -> sigma1 v = sigma2 v.
Hypothesis v1_neq_v3 : v1 <> v3.
Variable R : list register.
Variable phi1 : ltl_phi.
Hypothesis EQv3_1 : sigma1 v3 = (↓ R ,X (sigma1 v1) ../\ phi1).
Hypothesis EQv3_2 : sigma2 v3 = (↓ R ,X (var v1) ../\ phi1).
Hypothesis v1_not_Var_omega : ~ Var_omega v1.

Lemma normalize_store_X_1 :
  forall l,
  env_leq (Fpow_emp sigma2 l) (Fpow_emp sigma1 l).
Proof.
  induction l as [| l IHl].
  - (* base case *)
    unfold Fpow_emp, Fpow.
    now unfold env_leq.
  - (* inductive step *)
    unfold env_leq.
    intros v i j th th' x.
    unfold Fpow_emp, Fpow, F.
    intros H.
    destruct H as [H | H];
      [left | (right; apply H)].
    destruct (Var_eq_dec v v3)
      as [v_eq_v3 | v_neq_v3].
    + (* when v = v3 *)
      rewrite v_eq_v3, EQv3_1.
      rewrite v_eq_v3, EQv3_2 in H.
      inversion H as [|
        | i' j' th1 th2 x' R' p1 p2 Hij Hp1 Hv1
          EQi' EQj' EQth1 EQth2 EQx' [EQR' EQp1 EQp2] | |];
        clear i' EQi' j' EQj' th1 EQth1 th2 EQth2 x' EQx'
          R' EQR' p1 EQp1 p2 EQp2.
      apply models_fin_STORE_X; auto.
      clear H Hp1.
      inversion Hv1 as
        [i' j' th1 th2 x' v' Hij' Hf
         EQi' EQj' EQth1 EQth2 EQx' EQv' | | | |];
        clear i' EQi' j' EQj' th1 EQth1 th2 EQth2 x' EQx'
          v' EQv' Hv1.
      apply IHl in Hf.
      apply Fpow_is_monotonic in Hf.
      unfold Fpow_emp, Fpow, F in Hf.
      destruct Hf as [Hf | Hf].
      * apply Hf.
      * destruct Hf as [v1_omega _].
        now apply v1_not_Var_omega in v1_omega.
    + (* when v <> v3 *)
      rewrite (sigma_equiv _ v_neq_v3).
      apply (models_fin_is_monotonic _ _ IHl).
      apply H.
Qed.

Lemma normalize_store_X_2 :
  forall l,
  env_leq (Fpow_emp sigma1 l) (Fpow_emp sigma2 (2 * l)).
Proof.
  intros l.
  simpl.
  rewrite<- (plus_n_O l).
  induction l as [| l IHl].
  - (* base case *)
    unfold Fpow_emp, Fpow.
    now unfold env_leq.
  - (* inductive step *)
    simpl.
    unfold env_leq.
    rewrite<- (plus_n_Sm l l).
    intros v i j th th' x.
    unfold Fpow_emp, Fpow, F.
    intros H.
    destruct H as [H | H];
      [left | (right; apply H)].
    destruct (Var_eq_dec v v3)
      as [v_eq_v3 | v_neq_v3].
    + (* when v = v3 *)
      rewrite v_eq_v3, EQv3_2.
      rewrite v_eq_v3, EQv3_1 in H; clear v v_eq_v3.
      inversion H as [|
        | i' j' th1 th2 x' R' p1 p2 Hij Hp1 Hv1
          EQi' EQj' EQth1 EQth2 EQx' [EQR' EQp1 EQp2] | |];
        clear i' EQi' j' EQj' th1 EQth1 th2 EQth2 x' EQx'
          R' EQR' p1 EQp1 p2 EQp2 H.
      apply models_fin_STORE_X; auto.
      apply (models_fin_is_monotonic _ _ IHl) in Hv1.
      apply models_fin_var; auto.
      left.
      now rewrite (sigma_equiv _ v1_neq_v3) in Hv1.
    + (* when v <> v3 *)
      rewrite <- (sigma_equiv _ v_neq_v3).
      apply (models_fin_is_monotonic _ _ IHl) in H.
      apply (models_fin_is_monotonic _ _
        (Fpow_is_monotonic sigma2 (l + l))) in H.
      apply H.
Qed.

Theorem normalize_store_X :
  env_eq (lfpF sigma1) (lfpF sigma2).
Proof.
  unfold env_eq.
  split;
  unfold env_leq;
  intros v i j th th' x;
  rewrite lfpF_is_sup_Fpow;
  rewrite lfpF_is_sup_Fpow;
  intros [l H].
  - exists (2 * l).
    now apply normalize_store_X_2.
  - exists l.
    now apply normalize_store_X_1.
Qed.

End NormalizeStoreX.

End NormalForms.

(* Unused variables are not matter *)

Section UnusedVar.

Inductive usedVar : ltl -> Ensemble Var :=
  | usedVar_VAR : forall v,
      In _ (usedVar (var v)) v
  | usedVar_OR : forall v psi1 psi2,
      In _ (Union _ (usedVar psi1) (usedVar psi2)) v
      -> In _ (usedVar (psi1 .\/ psi2)) v
  | usedVar_STORE_X : forall v R psi phi,
      In _ (usedVar psi) v
      -> In _ (usedVar (↓ R,X psi ../\ phi)) v
  .

Lemma used_var_in_subformula_OR :
  forall p1 p2 : ltl,
  forall vs : Ensemble Var,
    Included _ (usedVar (p1 .\/ p2)) vs ->
    Included _ (usedVar p1) vs /\
    Included _ (usedVar p2) vs.
Proof.
  intros p1 p2 vs H.
  split; intros v Hv;
  apply H, usedVar_OR;
  [apply Union_introl | apply Union_intror];
  auto.
Qed.
Lemma used_var_in_subformula_STORE_X :
  forall (psi : ltl) phi R,
  forall vs : Ensemble Var,
    Included _ (usedVar (↓ R,X psi ../\ phi)) vs ->
    Included _ (usedVar psi) vs.
Proof.
  intros psi phi R vs H.
  intros v Hv.
  now apply H, usedVar_STORE_X.
Qed.

Variables sigma1 sigma2 : eqn_sys.
Variable vars : Ensemble Var.
Hypothesis sigma_equiv :
  forall v, In _ vars v -> sigma1 v = sigma2 v.
Hypothesis include_used_var :
  forall v, In _ vars v -> Included _ (usedVar (sigma1 v)) vars.

Lemma unused_var_not_matter :
  forall ell i j theta theta' x,
  forall v, In _ vars v ->
    Fpow_emp sigma1 ell v i j theta theta' x
    <-> Fpow_emp sigma2 ell v i j theta theta' x.
Proof.
  intros ell.
  induction ell as [| ell IH];
    intros i j theta theta' x v Hv.
  - (* base case (ell = 0) *)
    unfold Fpow_emp, Fpow.
    reflexivity.
  - (* inductive step on ell *)
    specialize (include_used_var v Hv).
    unfold Fpow_emp, Fpow, F.
    rewrite <- (sigma_equiv v Hv).

    split;
    intros H;
    destruct H as [H | H];
    [ left | (right; apply H)
    | left | (right; apply H)];
    generalize dependent x;
    generalize dependent theta';
    generalize dependent theta;
    generalize dependent j;
    generalize dependent i;

    induction (sigma1 v) as [v'
      | l1 IH1 l2 IH2 | R l1 IH1 phi | phi];
      intros i j th th' x H.
    + (* when sigma1 v = var v' *)
      assert (Hv': In _ vars v').
      { apply include_used_var, usedVar_VAR. }
      inversion H;
      apply models_fin_var; auto;
      apply IH; auto.
    + (* when sigma1 v = l1 .\/ l2 *)
      apply used_var_in_subformula_OR in include_used_var.
      destruct include_used_var as [Hvl1 Hvl2].
      inversion_clear H as [
        | i' j' th1 th2 x' l1' l2' Hij H' EQi' EQj' EQth1 EQth2 EQx' [EQl1' EQl2']
        | | |];
      apply models_fin_OR; auto.
      destruct H' as [H | H];
      [left | right];
      [apply IH1 | apply IH2]; auto.
    + (* when sigma1 v = ↓ R,X l1 ../\ phi *)
      apply used_var_in_subformula_STORE_X in include_used_var.
      inversion_clear H as [|
        | i' j' th1 th2 x' R' l1' phi' Hij Hphi H'
          EQi' EQj' EQth1 EQth2 EQx' [EQR' EQl1' EQphi'] | |];
      apply models_fin_STORE_X; auto.
    + (* when sigma1 v = φ phi *)
      inversion_clear H as [| |
       | i' j' th1 Hij | i' j' th1 phi' nphitt Hij Hphi].
      * (* when phi = [tt] *)
        apply models_fin_TT; auto.
      * (* when phi <> [tt] *)
        apply models_fin_PHI; auto.

    + (* when sigma1 v = var v', for <- *)
      assert (Hv': In _ vars v').
      { apply include_used_var, usedVar_VAR. }
      inversion H;
      apply models_fin_var; auto;
      apply IH; auto.
    + (* when sigma1 v = l1 .\/ l2, for <- *)
      apply used_var_in_subformula_OR in include_used_var.
      destruct include_used_var as [Hvl1 Hvl2].
      inversion_clear H as [
        | i' j' th1 th2 x' l1' l2' Hij H' EQi' EQj' EQth1 EQth2 EQx' [EQl1' EQl2']
        | | |];
      apply models_fin_OR; auto.
      destruct H' as [H | H];
      [left | right];
      [apply IH1 | apply IH2]; auto.
    + (* when sigma1 v = ↓ R,X l1 ../\ phi, for <- *)
      apply used_var_in_subformula_STORE_X in include_used_var.
      inversion_clear H as [|
        | i' j' th1 th2 x' R' l1' phi' Hij Hphi H'
          EQi' EQj' EQth1 EQth2 EQx' [EQR' EQl1' EQphi'] | |];
      apply models_fin_STORE_X; auto.
    + (* when sigma1 v = φ phi, for <- *)
      inversion_clear H as [| |
       | i' j' th1 Hij | i' j' th1 phi' nphitt Hij Hphi].
      * (* when phi = [tt] *)
        apply models_fin_TT; auto.
      * (* when phi <> [tt] *)
        apply models_fin_PHI; auto.
Qed.

End UnusedVar.
