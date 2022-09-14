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
  .

Notation "'(' i ',' theta '|=' u ',' psi ')'"
  := (models u i theta psi).

(* Equality of two ltl formulas *)

Axiom ltl_extensionality :
  forall psi1 psi2 : ltl,
    (forall i theta u, (i, theta |= u, psi1) <-> (i, theta |= u, psi2))
    -> psi1 = psi2.

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

Lemma phi_eq_xtt_phi : forall phi : ltl_phi,
  (φ phi) = ↓ nil ,X (φ [tt]) ../\ phi.
Proof.
  intro phi.
  apply ltl_extensionality.
  intros i theta u;
  split; intro H.
  - (* phi -> Xtt ../\ phi *)
  apply models_STORE_X.
  + (* models_phi i theta phi *)
  now inversion H.
  + (* tt *)
  apply models_PHI.
  now apply models_pos.
  - (* Xtt ../\ phi -> phi *)
  apply models_PHI.
  now inversion H.
Qed.

Lemma psi_eq_psi_or_ff : forall psi : ltl,
  psi = (psi .\/ (φ ~[tt])).
Proof.
  intro psi.
  apply ltl_extensionality.
  intros i theta u;
  split; intro H.
  - (* psi -> psi .\/ ff *)
  apply models_OR.
  now left.
  - (* psi .\/ ff -> psi *)
  inversion H as [|j th p1 p2 H1| |].
  destruct H1 as [H1 | H1]; auto.
  clear H2;
  inversion H1 as [| | |j' th' p1' H2].
  clear H3;
  inversion H2 as [|a H3|].
  unfold models_atom in H3.
  contradiction.
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

Axiom tt_Vtt_or_Var_omega :
  forall (sigma : eqn_sys) (v : Var),
  sigma v = (φ [tt]) ->
  v = Vtt \/ Var_omega v.

Axiom sigma_injective_on_Var_omega :
  forall (sigma : eqn_sys) (v1 v2 : Var),
  Var_omega v1 ->
  sigma v1 = sigma v2 -> v1 = v2.


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
