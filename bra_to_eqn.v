(*
 * mu-calculus for infinite data words:
 * Definitions about converting a Buchi automaton to equations
 *)

Require Import ltl.
Require Import automata.

Section Auxiliaries.

Lemma Forall_In {T : Type} :
  forall (l : list T),
    Forall (fun x => In x l) l.
Proof.
  intro l.
  rewrite Forall_forall.
  intros x H; assumption.
Qed.

Lemma neg_exists_eq_forall :
  forall (T : Type) (P : T -> Prop),
  ~ (exists q : T, P q) <-> (forall q : T, ~ P q).
Proof.
  intros T P; split.
  - intros H q pq; apply H; now exists q.
  - intros H [q pq]; now apply (H q).
Qed.

End Auxiliaries.

Section BRAToEqn.

Variable A : automaton.

Hypothesis epsilon_free :
  forall q R q',
  ~ transitions A q epsilon R q'.

Hypothesis at_least_one_transition :
  forall q,
  exists phi R q', transitions A q (Σφ phi) R q'.

(** object-to-variable functions **)

Parameter QVar : states A -> Var.
Parameter RVar : states A -> SigmaE -> list register -> states A -> Var.

Definition rule := (states A * SigmaE * list register * states A)%type.
Parameter deltaq : states A -> list rule.
Axiom deltaq_intro :
  forall q a R q',
    transitions A q a R q' ->
    In (q, a, R, q') (deltaq q).
Axiom deltaq_inv :
  forall q q1 a R q',
    In (q, a, R, q') (deltaq q1) ->
    q1 = q /\ transitions A q a R q'.

Parameter QDVar : list rule -> Var.

Axiom QDVar_injective :
  forall l1 l2, QDVar l1 = QDVar l2 -> l1 = l2.
Axiom QDVar_neq_RVar :
  forall l q a R q', QDVar l <> RVar q a R q'.

(** sigmaA is the eqn_sys obtained from A **)

Parameter sigmaA : eqn_sys.

Fixpoint sigmaA_QDVar (l : list rule) : Prop :=
  match l with
  | nil => sigmaA (QDVar nil) = (φ ~[tt])
  | (q, a, R, q') :: t =>
      sigmaA (QDVar l) =
        (var (RVar q a R q') .\/ var (QDVar t))
      /\ sigmaA_QDVar t
  end.

Axiom sigmaA_Q :
  forall q : states A,
  sigmaA (QVar q) = (var (QDVar (deltaq q)) .\/ var (QDVar (deltaq q)))
  /\ sigmaA_QDVar (deltaq q).

Axiom sigmaA_R :
  forall q phi R q',
    transitions A q (Σφ phi) R q' ->
    sigmaA (RVar q (Σφ phi) R q') =
      (↓ R ,X (var (QVar q')) ../\ phi).

Axiom sigmaA_Var_omega :
  forall q,
  finals A q <-> Var_omega (QVar q).


Lemma deltaq_neq_nil :
  forall q, deltaq q <> nil.
Proof.
  intros q H.
  specialize (at_least_one_transition q).
  destruct at_least_one_transition as [phi [R [q' Ht]]].
  apply deltaq_intro in Ht.
  rewrite H in Ht.
  inversion Ht.
Qed.

Lemma deltaq_injective :
  forall q q',
    deltaq q = deltaq q' -> q = q'.
Proof.
  intros q q' H.
  remember (deltaq q) as dq eqn: EQdq.
  destruct dq.
  - (* When deltaq q = nil *)
  symmetry in EQdq.
  now apply deltaq_neq_nil in EQdq.
  - (* When delta q = a :: dq *)
  assert (Hrq : In r (deltaq q)).
  { rewrite<- EQdq; unfold In; now left. }
  assert (Hrq' : In r (deltaq q')).
  { rewrite<- H; unfold In; now left. }
  destruct r as [[[q1 a] R] q1'].
  apply deltaq_inv in Hrq.
  apply deltaq_inv in Hrq'.
  destruct Hrq as [EQq _].
  destruct Hrq' as [EQq' _].
  rewrite EQq.
  rewrite EQq'.
  reflexivity.
Qed.

Lemma sigmaA_QVar_injective :
  forall q q',
    sigmaA (QVar q) = sigmaA (QVar q') ->
    q = q'.
Proof.
  intros q q' H.
  destruct (sigmaA_Q q) as [Hsq _].
  destruct (sigmaA_Q q') as [Hsq' _].
  rewrite <- H in Hsq'.
  rewrite Hsq' in Hsq.
  injection Hsq.
  intros _ Hqd.
  apply QDVar_injective in Hqd.
  now apply deltaq_injective.
Qed.

Lemma sigmaA_RVar_neq_sigmaA_QVar :
  forall q1 q2 q a R,
    transitions A q1 a R q2 ->
    sigmaA (RVar q1 a R q2) <> sigmaA (QVar q).
Proof.
  intros q1 q2 q a R Hrule H.
  destruct (sigmaA_Q q) as [Hsq _].
  rewrite Hsq in H; clear Hsq.
  destruct a as [|phi];
  try (apply epsilon_free in Hrule; contradiction).
  assert (Hr := sigmaA_R q1 phi R q2 Hrule).
  rewrite Hr in H.
  discriminate H.
Qed.

Lemma sigmaA_QDVar_neq_sigmaA_QVar :
  forall l q,
    sigmaA_QDVar l ->
    sigmaA (QDVar l) <> sigmaA (QVar q).
Proof.
  intros l q Hsqd H.
  destruct (sigmaA_Q q) as [Hsq _].
  rewrite Hsq in H; clear Hsq.
  destruct l as [|r l'].
  - unfold sigmaA_QDVar in Hsqd.
  rewrite Hsqd in H.
  discriminate H.
  - destruct r as [[[q1 a] R] q'].
  unfold sigmaA_QDVar in Hsqd;
  destruct Hsqd as [Hsqd _].
  rewrite Hsqd in H.
  injection H.
  intros _ Hrqd.
  symmetry in Hrqd.
  now apply QDVar_neq_RVar in Hrqd.
Qed.

Lemma sigmaA_QDVar_sublist :
  forall l l',
    sigmaA_QDVar (l ++ l') -> sigmaA_QDVar l'.
Proof.
  intros l l' H.
  induction l as [| [[[q a] R] q'] l IH];
    simpl in H; auto.
  destruct H as [_ H].
  apply IH, H.
Qed.

Section CorrectnessOfSigmaA.

(*** AA is the automaton obtained from sigmaA ***)

Let AA := EqnBRA sigmaA.

(*** AA simulates A ***)

Lemma move_QVar_to_QDVar :
  forall q i theta,
  move (A:=AA)
    (sigmaA (QVar q), theta, i)
    (sigmaA (QDVar (deltaq q)), theta, i).
Proof.
  intros q i theta.
  destruct (sigmaA_Q q) as [Hsq _].
  apply (move_epsilon (A:=AA)).
  rewrite Hsq.
  apply (RuleA_OR_left sigmaA).
Qed.

Lemma moveStar_QVar_to_RVar :
  forall q q' a R i theta,
    transitions A q a R q' ->
    moveStar (A:=AA)
      (sigmaA (QVar q), theta, i)
      (sigmaA (RVar q a R q'), theta, i).
Proof.
  intros q q' a R i theta Ht.
  destruct (sigmaA_Q q) as [_ Hdq].
  apply (move_moveStar (A:=AA))
    with (c2:=(sigmaA (QDVar (deltaq q)), theta, i));
  try apply move_QVar_to_QDVar.
  apply deltaq_intro in Ht.
  induction (deltaq q) as [| r t IH].
  - (* When deltaq q = nil *)
  now unfold In in Ht.
  - (* When deltaq q = r :: t *)
  apply in_inv in Ht.
  destruct Ht as [Ht | Ht].
  + (* When r = (q, a, R, q') *)
  rewrite Ht in Hdq.
  unfold sigmaA_QDVar in Hdq;
  destruct Hdq as [Hdq _].
  apply (move_moveStar (A:=AA))
    with (c2:=(sigmaA (RVar q a R q'), theta, i));
  try apply moveStar_refl.
  apply (move_epsilon (A:=AA)).
  rewrite <- Ht in Hdq.
  rewrite Hdq.
  apply RuleA_OR_left.
  + (* When In r t *)
  destruct r as [[[q1 a1] R1] q'1].
  unfold sigmaA_QDVar in Hdq;
  destruct Hdq as [Hdq Hdq1].
  specialize (IH Ht Hdq1); clear Hdq1.
  rewrite Hdq; clear Hdq.
  apply (move_moveStar (A:=AA))
    with (c2:=(sigmaA (QDVar t), theta, i));
  try assumption.
  apply (move_epsilon (A:=AA)).
  apply RuleA_OR_right.
Qed.

Lemma move_RVar_to_QVar :
  forall q q' phi R i theta theta',
    transitions A q (Σφ phi) R q' ->
    models_phi i theta phi ->
    theta' = updateR theta R (snd (Str_nth i w)) ->
    move (A:=AA)
      (sigmaA (RVar q (Σφ phi) R q'), theta, i)
      (sigmaA (QVar q'), theta', S i).
Proof.
  intros q q' phi R i theta theta' Ht Hm EQth'.
  rewrite sigmaA_R; auto.
  rewrite EQth'; clear EQth'.
  apply (move_action (A:=AA)) with phi; auto.
  apply RuleA_STORE_X.
Qed.

Lemma moveStar_QVar_to_QVar :
  forall q q' i j theta theta',
    move (A:=A) (q, theta, i) (q', theta', j) ->
    moveStar (A:=AA)
      (sigmaA (QVar q), theta, i)
      (sigmaA (QVar q'), theta', j).
Proof.
  intros q q' i j theta theta' Hm.
  inversion Hm
  as [phi R i1 q1 q2 th Ht Hmo [EQq1 EQth EQi1] [EQq2 EQth' HSij]
     |i1 q1 q2 th Ht].
  - (* When transitions A q (Σφ phi) R q' *)
  apply (moveStar_move (A:=AA))
  with (c2:=(sigmaA (RVar q (Σφ phi) R q'), theta, i)).
  + now apply moveStar_QVar_to_RVar.
  + apply move_RVar_to_QVar; auto.
  - (* When transitions A q epsilon ... *)
  now apply epsilon_free in Ht.
Qed.

Theorem AA_simulates_A :
  forall q q' i j theta theta',
    moveStar (A:=A) (q, theta, i) (q', theta', j) ->
    moveStar (A:=AA)
      (sigmaA (QVar q), theta, i)
      (sigmaA (QVar q'), theta', j).
Proof.
  intros q q' i j theta theta' H.
  remember (q, theta, i) as c1 eqn: EQc1.
  remember (q', theta', j) as c2 eqn: EQc2.
  generalize dependent i;
  generalize dependent theta;
  generalize dependent q.
  induction H as [|c1 c3 c2 Hm Hstar IH];
  intros q theta i EQc1.
  - rewrite EQc2 in EQc1.
  injection EQc1;
  intros EQj EQth' EQq'.
  rewrite EQj;
  rewrite EQth';
  rewrite EQq'.
  apply moveStar_refl.
  - specialize (IH EQc2).
  rewrite EQc1 in Hm; clear c1 EQc1.
  rewrite EQc2 in Hstar; clear c2 EQc2.
  destruct c3 as [[q3 th3] i3].
  specialize (IH q3 th3 i3 (refl_equal (q3, th3, i3))).
  apply moveStar_QVar_to_QVar in Hm.
  apply (moveStar_transitive (A:=AA))
    with (c2:=(sigmaA (QVar q3), th3, i3));
  auto.
Qed.

(*** A simulates AA ***)

(* Decidability of equality *)

Lemma neg_exists_P_forall_neg_P_open :
  forall q' : states AA,
    ~ (exists q, q' = (sigmaA (QVar q))) <->
    (forall q, q' <> (sigmaA (QVar q))).
Proof.
  intro q'.
  split; apply neg_exists_eq_forall.
Qed.

Hypothesis excluded_middle : forall P, P \/ ~P.

Lemma sigmaA_QVar_dec :
  forall q' : states AA,
    (exists q, q' = (sigmaA (QVar q))) \/
    (forall q, q' <> (sigmaA (QVar q))).
Proof.
  intros q'.
  rewrite <- neg_exists_P_forall_neg_P_open.
  apply excluded_middle.
Qed.

Lemma Q_eq_dec :
  forall q1 q2 : states A,
    q1 = q2 \/ q1 <> q2.
Proof.
  intros q1 q2;
  apply excluded_middle.
Qed.

(* Reachable states *)

Definition sigmaA_Var_state (q : states AA) : Prop :=
  (exists q', q = sigmaA (QVar q')) \/
  (exists q' a R q'', q = sigmaA (RVar q' a R q'') /\
    transitions A q' a R q'') \/
  (exists q' l l', q = sigmaA (QDVar l) /\
    l' ++ l = deltaq q').

Lemma sigmaA_Var_state_can_only_move_to_sigmaA_Var_state :
  forall q1 q2 th th' i j,
    move (A:=AA) (q1, th, i) (q2, th', j) ->
    sigmaA_Var_state q1 ->
    sigmaA_Var_state q2.
Proof.
  intros q1 q2 th th' i j Hm Hq1.
  unfold sigmaA_Var_state in Hq1.
  destruct Hq1 as [Hq1 | [Hq1 | Hq1]].
  + (* when q1 = sigmaA (QVar q') *)
    destruct Hq1 as [q' Hq1].
    rewrite Hq1 in Hm.
    destruct (sigmaA_Q q') as [EQsa _].
    inversion Hm as
      [phi R i'1 q'1 q'2 th'1 Ht Hmp
        [EQq'1 EQth'1 EQi'1] [EQq'2 EQth1 EQi']
      | i'1 q'1 q'2 th'1 Ht
        [EQq'1 EQth'1 EQi'1] [EQq'2 EQth1 EQi']];
      clear i'1 EQi'1 q'1 EQq'1 q'2 EQq'2 th'1 EQth'1.
    * (* when non-epsilon-transition *)
      inversion Ht as [EQsa' EQphi EQR EQq1' | |
        | R' v phi' EQsa' EQphi' EQR' EQv];
        rewrite EQsa in EQsa';
        inversion EQsa'.
    * (* when epsilon-transition *)
      inversion Ht as [| v1 v2 EQsa' EQeps EQnil EQq1'
        | v1 v2 EQsa' EQeps EQnil EQq1' |];
        clear EQeps EQnil;
        rewrite EQsa in EQsa';
        injection EQsa';
        intros EQv2 EQv1;
        [rewrite EQv1 | rewrite EQv2];
        right; right;
        exists q', (deltaq q'), nil; auto.
  + (* when q1 = sigmaA (RVar q' a R q'') *)
    destruct Hq1 as [q' [a [R [q'' [Hq1 Hta]]]]].
    destruct a as [| phi];
      [(apply epsilon_free in Hta; contradiction) |].
    assert (EQsa := sigmaA_R q' phi R q'' Hta).
    rewrite Hq1 in Hm.
    inversion Hm as
      [phi' R' i'1 q'1 q'2 th'1 Ht Hmp
        [EQq'1 EQth'1 EQi'1] [EQq'2 EQth EQi]
      | i'1 q'1 q'2 th'1 Ht
        [EQq'1 EQth'1 EQi'1] [EQq'2 EQth EQi]];
      clear i'1 EQi'1 q'1 EQq'1 q'2 EQq'2 th'1 EQth'1.
    * (* when non-epsilon-transition *)
      inversion Ht as [EQsa' EQphi EQR' EQq2 | |
        | R'' v phi'' EQsa' EQphi' EQR' EQq2];
        rewrite EQsa in EQsa'.
      -- inversion EQsa'.
      -- injection EQsa';
        intros EQphi'' EQv EQR''.
        rewrite EQv.
        left.
        now exists q''.
    * (* when epsilon-transition *)
      inversion Ht as [| v1 v2 EQsa' EQeps EQnil EQq1'
        | v1 v2 EQsa' EQeps EQnil EQq1' |];
        clear EQeps EQnil;
        rewrite EQsa in EQsa';
        inversion EQsa'.
  + (* when q1 = sigmaA (QDVar l) *)
    destruct Hq1 as [q [l [l' [Hq1 Hl]]]].
    destruct (sigmaA_Q q) as [EQsaq EQsa].
    rewrite <- Hl in EQsa.
    apply sigmaA_QDVar_sublist in EQsa.
    rewrite Hq1 in Hm.
    inversion Hm as
      [phi' R' i'1 q'1 q'2 th'1 Ht Hmp
        [EQq'1 EQth'1 EQi'1] [EQq'2 EQth EQi]
      | i'1 q'1 q'2 th'1 Ht
        [EQq'1 EQth'1 EQi'1] [EQq'2 EQth EQi]];
      clear i'1 EQi'1 q'1 EQq'1 q'2 EQq'2 th'1 EQth'1.
    * (* when non-epsilon-transition *)
      inversion Ht as [EQsa' EQphi EQR' EQq2 | |
        | R'' v phi'' EQsa' EQphi' EQR' EQq2];
        destruct l as [| [[[q' a] R] q''] l];
        [| destruct EQsa as [EQsa _] |
         | destruct EQsa as [EQsa _]];
        rewrite EQsa in EQsa';
        inversion EQsa'.
    * (* when epsilon-transition *)
      inversion Ht as [| v1 v2 EQsa' EQeps EQnil EQq1'
        | v1 v2 EQsa' EQeps EQnil EQq1' |];
        clear EQeps EQnil;
        destruct l as [| [[[q' a] R] q''] l];
        [(rewrite EQsa in EQsa'; inversion EQsa') | |
         (rewrite EQsa in EQsa'; inversion EQsa') |];
        destruct EQsa as [EQsa _];
        rewrite EQsa in EQsa';
        injection EQsa';
        intros EQv2 EQv1;
        [rewrite EQv1 | rewrite EQv2].
      -- (* to show sigmaA_Var_state (sigmaA (RVar q' a R q'')) *)
        right; left.
        exists q', a, R, q''.
        split; auto.
        assert (Hin: In (q', a, R, q'') (deltaq q)).
        {
          rewrite <- Hl.
          apply in_or_app.
          right.
          apply in_eq.
        }
        apply deltaq_inv in Hin.
        destruct Hin as [EQq Hin].
        apply Hin.
      -- (* to show sigmaA_Var_state (sigmaA (QDVar l)) *)
        right; right.
        exists q, l, (l' ++ ((q',a,R,q'')::nil)).
        split; auto.
        rewrite <- Hl.
        rewrite app_ass.
        now simpl.
Qed.

Theorem only_sigmaA_Var_states_are_reachable :
  forall q1 q2 th th' i j,
    moveStar (A:=AA) (q1, th, i) (q2, th', j) ->
    sigmaA_Var_state q1 ->
    sigmaA_Var_state q2.
Proof.
  intros q1 q2 th th' i j Hm Hq1.
  remember (q1, th,  i) as c1 eqn: EQc1;
  remember (q2, th', j) as c2 eqn: EQc2.
  generalize dependent i;
  generalize dependent th;
  generalize dependent q1.
  induction Hm as [c1 | c1 c2 c3 H12 H23 IH];
    intros q1 Hq1 th i EQc1.
  - (* base case (c1 = c2) *)
    rewrite EQc1 in EQc2.
    injection EQc2;
      intros EQi EQth EQq2.
    now rewrite <- EQq2.
  - (* inductive step *)
    specialize (IH EQc2).
    destruct c2 as [[q2' th2] i2].
    rewrite EQc1 in H12.
    apply sigmaA_Var_state_can_only_move_to_sigmaA_Var_state in H12;
    auto.
    now apply (IH _ H12 th2 i2).
Qed.

(*** (move AA)^+ not going thru sigmaA QVar ***)

Inductive movePlus_without_QVar
  : config AA -> config AA -> Prop :=
  | movePlus_without_QVar_step :
      forall c1 c2,
      move (A:=AA) c1 c2 ->
      movePlus_without_QVar c1 c2
  | movePlus_without_QVar_trans :
      forall c1 c2 c3 : config AA,
      (forall q,
       match c2 with (q2, _, _) =>
         (q2 <> (sigmaA (QVar q))) end) ->
      move (A:=AA) c1 c2 ->
      movePlus_without_QVar c2 c3 ->
      movePlus_without_QVar c1 c3
  .

(* Simulate one middle step *)

Lemma RVar_to_QVar_one_step :
  forall q q' a R i j theta theta',
    transitions A q a R q' ->
    movePlus_without_QVar
      (sigmaA (RVar q a R q'), theta, i)
      (sigmaA (QVar q'), theta', j) ->
    move (A:=A) (q, theta, i) (q', theta', j).
Proof.
  intros q q' a R i j theta theta';
  intros Ht Hpl.
  destruct a as [|phi];
  try (apply epsilon_free in Ht; contradiction).
  assert (Hsrq := sigmaA_R q phi R q' Ht).
  inversion Hpl
  as [c1 c2 H12 EQc1 EQc2
     |c1 c2 c3 Hc2 H12 H23 EQc1 EQc3];
  inversion H12
  as [phi1 R1 i1 q1 q2 th HtAA Hphi1 [EQq1 EQth EQi1] [EQq2 EQth' EQij]
     |i1 q1 q2 th HtAA [EQq1 EQth EQi1] [EQq2 EQth' EQij] ];
  clear q1 EQq1 th EQth i1 EQi1;
  inversion HtAA
  as [EQsrq EQphi1 EQR1 EQsq'
     |v1 v2 EQsrq EQeps EQnil EQsq'
     |v1 v2 EQsrq EQeps EQnil EQsq'
     |R2 v2 phi2 EQsrq EQphi1 EQR1 EQsq'];
  rewrite Hsrq in EQsrq;
  try discriminate EQsrq;
  injection EQsrq;
  intros EQphi2 EQv2 EQR2;
  rewrite EQR2 in EQR1;
  rewrite EQphi2 in EQphi1;
  rewrite <- EQphi1 in Hphi1;
  clear EQsrq R2 EQR2 phi2 EQphi2.
  - (* c1 |- c2 *)
  rewrite <- EQR1;
  apply move_action with phi; auto.
  - (* c1 |- c2 |-^+ c3 *)
  rewrite EQv2 in EQsq';
  rewrite <- EQsq' in EQq2;
  rewrite <- EQR1 in EQq2;
  clear v2 EQv2.
  rewrite <- EQq2 in Hc2.
  specialize (Hc2 q').
  contradiction.
Qed.

Lemma QDVar_to_QVar_one_step :
  forall q q' l i j theta theta',
    sigmaA_QDVar l ->
    Forall (fun x => In x (deltaq q)) l ->
    movePlus_without_QVar
      (sigmaA (QDVar l), theta, i)
      (sigmaA (QVar q'), theta', j) ->
    move (A:=A) (q, theta, i) (q', theta', j).
Proof.
  intros q q' l i j theta theta'
    Hsqd Hdq Hpl.
  induction l as [| r t IHt].
  - (* When l = nil *)
  inversion Hsqd as [EQsqd].
  rewrite EQsqd in Hpl.
  inversion Hpl
  as [c1 c2 H12 EQc1 EQc2
     |c1 c2 c3 Hc2 H12 H23 EQc1 EQc3];
  inversion H12
  as [phi1 R1 i1 q1 q2 th HtAA Hphi1 [EQq1 EQth EQi1] [EQq2 EQth' EQij]
     |i1 q1 q2 th HtAA [EQq1 EQth EQi1] [EQq2 EQth' EQij] ];
  clear q1 EQq1 th EQth i1 EQi1;
  inversion HtAA.
  - (* When l = r::t *)
  destruct r as [[[q1 a] R] q2].
  destruct Hsqd as [Hsqd Hsqd'].
  rewrite Hsqd in Hpl.
  inversion Hdq as [|r' t' Hinq1 Hft [EQr' EQt']];
  clear r' EQr' t' EQt'.
  specialize (IHt Hsqd' Hft).
  inversion Hpl
  as [c1 c2 H12 EQc1 EQc2
     |c1 c2 c3 Hc2 H12 H23 EQc1 EQc3];
  inversion H12
  as [phi1 R2 i1 q1' q2' th HtAA Hphi1 [EQq1 EQth EQi1] [EQq2 EQth' EQij]
     |i1 q1' q2' th HtAA [EQq1 EQth EQi1] [EQq2 EQth' EQij] ];
  clear q1' EQq1 th EQth i1 EQi1;
  inversion HtAA
  as [EQsrq EQphi1 EQR1 EQsq'
     |v1 v2 [EQv1 EQv2] EQeps EQnil EQsq'
     |v1 v2 EQsrq EQeps EQnil EQsq'
     |R3 v2 phi2 EQsrq EQphi1 EQR1 EQsq'];
  try clear EQeps EQnil;
  apply deltaq_inv in Hinq1;
  destruct Hinq1 as [EQq1 Hinq1].
  + (* When sigmaA (RVar r) = sigmaA (QVar q') *)
  apply sigmaA_RVar_neq_sigmaA_QVar in EQsq'; auto;
  contradiction.
  + (* When sigmaA (QDVar t) = sigmaA (QVar q') *)
  apply sigmaA_QDVar_neq_sigmaA_QVar in EQsq'; auto;
  contradiction.
  + (* When sigmaA (RVar r) = q2' *)
  clear v1 EQv1 v2 EQv2.
  rewrite <- EQq1 in Hinq1;
  rewrite <- EQq1 in EQsq';
  rewrite <- EQsq' in EQq2;
  rewrite <- EQq2 in H23.
  clear Hpl HtAA q2' EQsq' Hc2.
  destruct (Q_eq_dec q' q2) as [Hq2 | Hq2].
  * (* When q' = q2 *)
  rewrite <- Hq2 in H23;
  rewrite <- Hq2 in Hinq1.
  apply RVar_to_QVar_one_step  in H23;
  auto.
  * (* When q' <> q2 *)
  destruct a as [| phi1];
  try (apply epsilon_free in Hinq1;
  contradiction).
  assert (Hrq2 := sigmaA_R q phi1 R q2).
  specialize (Hrq2 Hinq1).
  rewrite Hrq2 in H23.
  inversion H23
  as [c4 c5 H45 EQc4 EQc5
     |c4 c5 c6 Hc5 H45 H56 EQc4 EQc6].
  -- inversion H45
  as [phi2 R2 i2 q4 q5 th2 Ht45
     |i2 q4 q5 th2 Ht45].
  ++ inversion Ht45
  as [| | |R3 v3 p3 [EQR3 EQv3 EQp3] EQphi2 EQR2 EQsq2 ].
  apply (sigmaA_QVar_injective q2) in EQsq2.
  symmetry in EQsq2;
  apply Hq2 in EQsq2;
  contradiction.
  ++ inversion Ht45.
  -- inversion H45
  as [phi2 R2 i2 q4 q5 th2 Ht45 Hphi2 EQi2 EQc5
     |i2 q4 q5 th2 Ht45].
  ++ rewrite <- EQc5 in Hc5.
  inversion Ht45 as [| | |R3 v3 p3 EQR3 EQphi1 EQR2 EQsq2].
  symmetry in EQsq2;
  apply (Hc5 q2) in EQsq2;
  contradiction.
  ++ inversion Ht45.
  + (* When sigmaA (QDVar t) = q2' *)
  apply IHt.
  rewrite EQsq'.
  rewrite <- EQq2 in H23.
  apply H23.
Qed.

Lemma QVar_to_QVar_one_step :
  forall q q' i j theta theta',
    movePlus_without_QVar
      (sigmaA (QVar q), theta, i)
      (sigmaA (QVar q'), theta', j) ->
    move (A:=A) (q, theta, i) (q', theta', j).
Proof.
  intros q q' i j theta theta' Hpl.
  destruct (sigmaA_Q q) as [EQsq Hsqd].
  inversion Hpl
  as [c1 c2 H12 EQc1 EQc2
     |c1 c2 c3 Hc2 H12 H23 EQc1 EQc3];
  inversion H12
  as [phi1 R2 i1 q1' q2' th HtAA Hphi1 [EQq1 EQth EQi1] [EQq2 EQth' EQij]
     |i1 q1' q2' th HtAA [EQq1 EQth EQi1] [EQq2 EQth' EQij] ];
  clear q1' EQq1 th EQth i1 EQi1;
  inversion HtAA
  as [Hsq EQphi1 EQR1 EQsq'
     |v1 v2 [Hsq EQv2'] EQeps EQnil EQsq'
     |v1 v2 Hsq EQeps EQnil EQsq'
     |R3 v2 phi2 Hsq EQphi1 EQR1 EQsq'];
  try clear EQeps EQnil;
  rewrite EQsq in Hsq;
  try discriminate Hsq;
  injection Hsq;
  intros EQv2 EQv1;
  try rewrite EQv1 in EQsq';
  try rewrite EQv2 in EQsq';
  try (apply sigmaA_QDVar_neq_sigmaA_QVar in EQsq'; auto;
  contradiction);
  rewrite <- EQsq' in EQq2;
  rewrite <- EQq2 in H23;
  apply QDVar_to_QVar_one_step with (deltaq q); auto;
  apply Forall_In.
Qed.

(* 'Star' version of movePlus_without_QVar *)
Inductive moveStar_without_QVar
  : config AA -> config AA -> Prop :=
  | moveStar_without_QVar_refl :
      forall c1,
      moveStar_without_QVar c1 c1
  | moveStar_without_QVar_plus :
      forall c1 c2,
      movePlus_without_QVar c1 c2 ->
      moveStar_without_QVar c1 c2
  .

(*** Splitting moveStar at every visit of QVar *)

Inductive moveStar_split_at_QVar
  : config AA -> config AA -> Prop :=
  | moveStar_split_at_QVar_step :
      forall c1 c2,
      moveStar_without_QVar c1 c2 ->
      moveStar_split_at_QVar c1 c2
  | moveStar_split_at_QVar_trans :
      forall c1 c2 c3,
      movePlus_without_QVar c1 c2 ->
      (exists q, match c2 with (q2, _, _) =>
                 q2 = (sigmaA (QVar q)) end) ->
      moveStar_split_at_QVar c2 c3 ->
      moveStar_split_at_QVar c1 c3
  .

Lemma movePlus_without_QVar_implies_moveStar :
  forall c1 c2,
    movePlus_without_QVar c1 c2 ->
    moveStar c1 c2.
Proof.
  intros c1 c2 H.
  induction H as [c1 | c1 c2 c3 Hc2 H12 H23 IH].
  - apply move_moveStar with c2; auto.
  apply moveStar_refl.
  - now apply move_moveStar with c2.
Qed.

Lemma moveStar_without_QVar_implies_moveStar :
  forall c1 c2,
    moveStar_without_QVar c1 c2 ->
    moveStar c1 c2.
Proof.
  intros c1 c2 H.
  destruct H as [c1 | c1 c2].
  - apply moveStar_refl.
  - now apply movePlus_without_QVar_implies_moveStar.
Qed.

Lemma moveStar_eq_moveStar_split_at_QVar :
  forall c1 c2,
    moveStar (A:=AA) c1 c2 <->
    moveStar_split_at_QVar c1 c2.
Proof.
  intros c1 c2.
  split;
  intro H.
  - (* -> *)
  induction H as [| c1 c2 c3 Hmov Hstar IH].
  + apply moveStar_split_at_QVar_step.
  apply moveStar_without_QVar_refl.
  + destruct c2 as [[q2 th2] i2].
  destruct (sigmaA_QVar_dec q2) as [Hq2 | Hq2].
  * destruct Hq2 as [q EQq2].
  apply moveStar_split_at_QVar_trans
    with (c2:=(q2, th2, i2));
  try apply movePlus_without_QVar_step;
  auto.
  now exists q.
  * inversion IH as [c2 c3' IH'| c2 c2' c3' H1 H2 H3].
  -- apply moveStar_split_at_QVar_step.
  inversion IH';
  apply moveStar_without_QVar_plus.
  ++ now apply movePlus_without_QVar_step.
  ++ now apply movePlus_without_QVar_trans
    with (c2:=(q2, th2, i2)).
  -- apply moveStar_split_at_QVar_trans with c2';
  auto.
  now apply movePlus_without_QVar_trans
    with (c2:=(q2, th2, i2)).
  - (* <- *)
  induction H as [c1 c2 | c1 c2 c3 H12 Hc2 H23 IH].
  + now apply moveStar_without_QVar_implies_moveStar.
  + apply movePlus_without_QVar_implies_moveStar in H12.
  apply moveStar_transitive with c2; auto.
Qed.

(* Simulate any number of steps *)

Theorem A_simulates_AA :
  forall q q' i j theta theta',
    moveStar (A:=AA)
      (sigmaA (QVar q), theta, i)
      (sigmaA (QVar q'), theta', j) ->
    moveStar (A:=A) (q, theta, i) (q', theta', j).
Proof.
  intros q q' i j theta theta' H.
  apply moveStar_eq_moveStar_split_at_QVar in H.
  remember (sigmaA (QVar q), theta, i) as c1 eqn: EQc1;
  remember (sigmaA (QVar q'), theta', j) as c2 eqn: EQc2.
  generalize dependent theta;
  generalize dependent i;
  generalize dependent q.
  induction H
    as [c1 c2 Hstar | c1 c3 c2 H13 Hc3 H32 IH];
  intros q i theta EQc1.
  - (* When one step *)
  inversion Hstar as [c1' EQc1' EQc12|c1' c2' H12 EQc1' EQc2'].
  + (* When c1 = c2 *)
  rewrite EQc1 in EQc12;
  rewrite EQc2 in EQc12.
  injection EQc12;
  intros EQij EQth EQsq.
  apply sigmaA_QVar_injective in EQsq.
  rewrite <- EQsq;
  rewrite <- EQth;
  rewrite <- EQij.
  apply moveStar_refl.
  + (* When c1 |-+ c2 *)
  clear c1' EQc1' c2' EQc2'.
  rewrite EQc1 in H12;
  rewrite EQc2 in H12.
  apply move_moveStar with (q', theta', j);
  try apply moveStar_refl.
  apply QVar_to_QVar_one_step; assumption.
  - (* When multiple steps *)
  specialize (IH EQc2).
  destruct c3 as [[q3 th3] i3].
  destruct Hc3 as [q1 Hc3].
  rewrite Hc3 in H13;
  rewrite Hc3 in H32;
  rewrite Hc3 in IH;
  rewrite EQc1 in H13.
  specialize (IH q1 i3 th3 (refl_equal (sigmaA (QVar q1), th3, i3))).
  apply move_moveStar with (q1, th3, i3); auto.
  apply QVar_to_QVar_one_step; auto.
Qed.

End CorrectnessOfSigmaA.

End BRAToEqn.
