(*
 * mu-calculus for infinite data words:
 * Basic definition of LTL.
 *)

Require Export Nat Arith.
Require Export Lists.List.
Require Export Lists.Streams.
 
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

Parameter Var_omega : Var -> bool.

(* The transformation from Env to Env *)
Definition F (sigma : eqn_sys) (u : Env) : Env :=
  fun (v : Var) (i j : nat) (theta theta' : Theta) (x : Var) =>
  (i, theta; j, theta', x |= u, sigma v)
  \/ (Var_omega v = true /\ x = v /\ i = j /\ theta = theta').

(* power of F *)
Fixpoint Fpow (sigma : eqn_sys) (i : nat) (u : Env) : Env :=
  match i with
    0   => u
  | S n => F sigma (Fpow sigma n u)
  end.
Definition Fpow_emp sigma i := Fpow sigma i empty_env.

Parameter lfpF : Env.
Axiom lfpF_is_sup :
  forall (sigma : eqn_sys) v i j theta theta' x,
  lfpF v i j theta theta' x <->
  exists ell,
  Fpow_emp sigma ell v i j theta theta' x.

Lemma lfpF_is_upperbound :
  forall (sigma : eqn_sys) ell v i j theta theta' x,
  Fpow_emp sigma ell v i j theta theta' x ->
  lfpF v i j theta theta' x.
Proof.
  intros sigma ell v i j theta theta' x H.
  rewrite lfpF_is_sup.
  exists ell.
  apply H.
Qed.

(* The meaning of Vtt *)
Axiom sigma_Vtt : forall sigma : eqn_sys,
  sigma Vtt = (φ [tt]).

Axiom tt_Vtt_or_Var_omega :
  forall (sigma : eqn_sys) (v : Var),
  sigma v = (φ [tt]) ->
  v = Vtt \/ Var_omega v = true.

Axiom sigma_injective_on_Var_omega :
  forall (sigma : eqn_sys) (v1 v2 : Var),
  Var_omega v1 = true ->
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
