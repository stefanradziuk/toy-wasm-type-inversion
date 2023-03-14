From mathcomp Require Import ssreflect.
From Coq Require Import Program.Equality NArith ZArith_base List Floats.
Import ListNotations.

Notation " P ** Q " := (prod P Q) (at level 95, right associativity).

Inductive value : Set :=
  | val_i32: nat -> value
  | val_f32: float -> value
.

Inductive term : Set :=
  | term_const: value -> term
  | term_addi32
  | term_SEQ: term -> term -> term
.

Inductive value_type : Type :=
  | t_i32
  | t_f32
.

Inductive function_type : Type :=
  | Tf (t1s : list value_type) (t2s : list value_type)
.

Definition typeof (v : value) : value_type :=
  match v with
  | val_i32 _ => t_i32
  | val_f32 _ => t_f32
  end.

Inductive value_typing : value -> value_type -> Prop :=
  | vt: forall v, value_typing v (typeof v)
.

Inductive typing : term -> function_type -> Prop :=
  | typing_term_const : forall v vt,
      value_typing v vt -> typing (term_const v) (Tf [] [vt])
  | typing_term_addi32 : typing term_addi32 (Tf [t_i32; t_i32] [t_i32])
  | typing_weaken : forall t t1s t2s ts,
      typing t (Tf t1s t2s) -> typing t (Tf (ts ++ t1s) (ts ++ t2s))
  | typing_composition : forall t1 t2 t1s t2s t3s,
      typing t1 (Tf t1s t3s) ->
      typing t2 (Tf t3s t2s) ->
      typing (term_SEQ t1 t2) (Tf t1s t2s)
.

(* append induction on lists
 * the stdlib version uses Prop instead of Type *)
Lemma rev_list_ind_T :
  forall (A : Type) (P : list A -> Type),
  P [] ->
  (forall (a : A) (l : list A), P (rev l) -> P (rev (a :: l))) ->
  forall (l : list A), P (rev l).
Proof.
  intros A P Hemp Happ l.
  induction l as [|?? IHl].
  - apply Hemp.
  - apply Happ. apply IHl.
Qed.

Theorem rev_ind_T :
  forall (A : Type) (P : list A -> Type),
  P [] ->
  (forall (x : A) (l : list A), P l -> P (l ++ [x])) ->
  forall (l : list A), P l.
Proof.
  intros A P Hemp Happ l.
  induction l.
  - by apply Hemp.
  - assert (Hrev : a :: l = (rev (rev l ++ [a]))).
    { rewrite rev_unit. rewrite rev_involutive. by reflexivity. }
    rewrite Hrev.
    apply rev_list_ind_T.
    * by apply Hemp.
    * intros a' l' Hrevl'.
      simpl. apply Happ. by apply Hrevl'.
Qed.

(* Equality decidability lemmas *)
Lemma value_type_eq_dec : forall t1 t2 : value_type,
  {t1 = t2} + {t1 <> t2}.
Proof. decide equality. Qed.

Lemma value_type_list_eq_dec : forall l1 l2 : list value_type,
  {l1 = l2} + {l1 <> l2}.
Proof. apply List.list_eq_dec. apply value_type_eq_dec. Qed.

Lemma value_typing_deterministic : forall v vt1 vt2,
  value_typing v vt1 -> value_typing v vt2 -> vt1 = vt2.
Proof.
  intros ??? Hvt1 Hvt2.
  inversion Hvt1; inversion Hvt2; subst; try reflexivity; discriminate.
Qed.

(* Typing inversion lemmas *)
Lemma value_typing_inversion : forall v vt,
  value_typing v vt -> vt = typeof v.
Proof. intros v vt Hvtype. inversion Hvtype. reflexivity. Qed.

Lemma value_typing_inversion_i32 : forall v,
  value_typing v t_i32 -> {n & v = val_i32 n}.
Proof.
  intros v Hvtype. apply value_typing_inversion in Hvtype.
  destruct v; inversion Hvtype. exists n. reflexivity.
Defined.

Lemma value_typing_inversion_f32 : forall v,
  value_typing v t_f32 -> {f & v = val_f32 f}.
Proof.
  intros v Hvtype. apply value_typing_inversion in Hvtype.
  destruct v; inversion Hvtype. exists f. reflexivity.
Qed.

Lemma term_const_typing_inv : forall t v t1s t2s,
  t = (term_const v) ->
  typing t (Tf t1s t2s) ->
  {ts & t1s = ts /\ t2s = ts ++ [typeof v]}.
Proof.
  intros t v t1s t2s Hterm Htype. subst t.
  exists t1s; split => //.
  dependent induction Htype.
  - assert (Heqvt : vt0 = typeof v). { by apply value_typing_inversion. }
    rewrite Heqvt. by reflexivity.
  - rewrite <- app_assoc; f_equal.
    by apply IHHtype; reflexivity.
Qed.

Lemma term_addi32_typing_inv_nonempty : forall t1s t2s,
  typing term_addi32 (Tf t1s t2s) -> t2s <> [].
Proof.
  intros t1s' t2s' Htype'.
  dependent induction Htype'.
  - discriminate.
  - intros Hcontr. apply app_eq_nil in Hcontr as [_ Hcontr].
    apply IHHtype' with (t1s' := t1s) in Hcontr; try assumption; reflexivity.
Qed.

(* NOTE: had to do induction over Htype BEFORE splitting,
 * otherwise IH was useless *)
Lemma term_addi32_typing_inv : forall t1s t2s,
  typing term_addi32 (Tf t1s t2s) ->
  {ts & t1s = ts ++ [t_i32; t_i32] /\ t2s = ts ++ [t_i32]}.
Proof.
  intros t1s t2s Htype. exists (removelast t2s).
  dependent induction Htype => //.
  assert (IHHtype' :
    t1s0 = removelast t2s0 ++ [t_i32; t_i32] /\
    t2s0 = removelast t2s0 ++ [t_i32]
  ).
  { apply IHHtype with (t1s := t1s0); by reflexivity. }
  induction ts => //.
  assert (Ht2s0 : t2s0 <> []).
  { by apply (term_addi32_typing_inv_nonempty _ _ Htype). }
  assert (Hassoc : removelast ((a :: ts) ++ t2s0) = removelast ([a] ++ ts ++ t2s0)) => //.
  rewrite Hassoc. rewrite removelast_app. simpl.
  destruct IHts as [IHts1 IHts2].
  split; apply f_equal; by assumption.
  intros Hcontr.
  apply app_eq_nil in Hcontr as [_ Hcontr].
  apply Ht2s0 => //.
Defined.

(* We beed a type checker for the remaining lemmas *)

Definition type_checker_seq (t1 t2: term) (tf1 tf2: function_type): function_type :=
  (* TODO need to actually verify the types after the first n types
   * are correct *)
  match (tf1, tf2) with
  | (Tf t1_in t1_out, Tf t2_in t2_out) =>
      if length t1_out <=? length t2_in
      (* t2 consumes all or more than just the output of t1 *)
      then let ts := firstn (length t2_in - length t1_out) t2_in
      in Tf (ts ++ t1_in) (t2_out)
      (* t2 consumes some of the output of t1 *)
      else let ts := firstn (length t1_out - length t2_in) t1_out
      in Tf t1_in (ts ++ t2_out)
  end
.

Fixpoint type_checker (t: term): function_type :=
  match t with
  | term_const (val_i32 _) => Tf [] [t_i32]
  | term_const (val_f32 _) => Tf [] [t_f32]
  | term_addi32 => Tf [t_i32; t_i32] [t_i32]
  | term_SEQ t1 t2 =>
      type_checker_seq t1 t2 (type_checker t1) (type_checker t2)
  end.

Let i_17 := term_const (val_i32 17).
Let f_3_75 := term_const (val_f32 3.75).

Compute (type_checker i_17).
Compute (type_checker f_3_75).
Compute (type_checker (term_SEQ i_17 f_3_75)).
Compute (type_checker (term_SEQ (term_SEQ i_17 i_17) term_addi32)).
Compute (type_checker (term_SEQ i_17 (term_SEQ i_17 term_addi32))).

Axiom type_checker_implies_typing: forall t tf,
  type_checker t = tf ->
  typing t tf.

(* The weakenable relation needs to describe that the first function type
   can be weakened to the second. *)
Parameter weakenable: function_type -> function_type -> Prop.

Axiom typing_implies_type_checker_prefix: forall t tf,
  typing t tf ->
  weakenable (type_checker t) tf.

Lemma term_SEQ_typing_inv : forall t t1 t2 t1s t2s,
  t = term_SEQ t1 t2 ->
  typing t (Tf t1s t2s) ->
  {t3s & typing t1 (Tf t1s t3s) /\ typing t2 (Tf t3s t2s)}.
Proof.
  intros t t1 t2 t1s t2s Heqt Htype.
  destruct (type_checker t1) as [t1s' t1_t3s].
  destruct (type_checker t2) as [t2_t3s t2s'].

  (* note that t1_t3s is not necessarily equal to t2_t3s
   * (one of them may have an extra prefix) *)
  remember (length t2_t3s <=? length t1_t3s) as t1_t3s_longer.

  (* we can use the outer type (t1s'/t2s')
   * of the term with the longer 'inner' type (t1_t3s or t2_t3s)
   * to find out what prefix (ts') we need to put on our t3s
   * so that t1s/t2s match up with t1s'/t2s' *)

  remember (if t1_t3s_longer then t1s else t2s) as outer_type_expected.
  remember (if t1_t3s_longer then t1s' else t2s') as outer_type_minimal.
  remember (length outer_type_expected - length outer_type_minimal) as ts'_len.
  remember (firstn ts'_len outer_type_expected) as ts'.
  remember (if t1_t3s_longer then t1_t3s else t2_t3s) as longer_inner_type.
  exists (ts' ++ longer_inner_type).

  subst t.
  destruct t1_t3s_longer; subst longer_inner_type.
  - (* t1_t3s longer than t2_t3s *)
    dependent induction Htype => //.
    * (* weakening case *)
      give_up.
      (* eapply IHHtype. *)
      (* the IH here seems useless - it requires
       * t1s = t1s0, t2s = t2s0
       * is it maybe the case that ts = [] always? *)
    * (* composition case *)
      (* need to show ts' = [] *)
      subst outer_type_expected outer_type_minimal.
      (* assert (Ht1s : t1s = t1s'). { give_up. } *)
      assert (Hts' : ts' = []). { give_up. }
      rewrite Hts'. simpl.
      give_up.


  (* NOTE:
   * t1s    = t1s'   (modulo some prefix)
   * t2s    = t2s'   (modulo some prefix)
   * t1_t3s = t2_t3s (modulo some prefix) *)

  (* so we need to consider the two cases where
   * either t1_t3s is longer or t2_t3s is longer:
   *
   * - ts + t1_t3s = t2_t3s (t1_t3s shorter than t2_t3s)
   *
   *   so we can make the 'middle' types line up
   *   by weakening the left function type:
   *   (Tf (ts + t1s') (ts + t1_t3s)) . (Tf t2_t3s t2s')
   *
   *   so the minimal type for the composition is
   *   Tf (ts + t1s') t2s'
   *
   *   however, we may be dealing with a weakened version of that:
   *   Tf (ts' + ts + t1s') (ts' + t2s')
   *   and so the t3s we need is (ts' + t2_t3s)
   *
   * - t1_t3s = ts + t2_t3s (t1_t3s longer than t2_t3s)
   *
   *   so we can make the 'middle' types line up
   *   by weakening the right function type:
   *   (Tf t1s' t1_t3s) . (Tf (ts + t2_t3s) (ts + t2s'))
   *
   *   so the minimal type for the composition is
   *   Tf t1s' (ts + t2s')
   *
   *   however, we may be dealing with a weakened version of that:
   *   Tf (ts' + t1s') (ts' + ts + t2s')
   *   and so the t3s we need is (ts' + t1_t3s)
   *
   *
   *   so we have:
   *   exists ts ts',
   *     t1s = ts' + ts + t1s' /\ t2s = ts' + t2s' \/
   *     t1s = ts' + t1s' /\ t2s = ts' + ts + t2s'
   *   (and we can tell in which \/ branch we are based on lengths of
   *   t1_t3s/t2_t3s)
   *
   *)

  (* XXX need type checker correctness proof here *)
  (* XXX need to use the fact that the type checker's result is the
   * smallest/'strongest' possible type (?) *)
  (* XXX what is needed to show that t3s' = t3s'' (modulo a prefix on either)
   * may be able to use the internals of the type checker somehow? *)
  (* actually probably can just invert Htype for that,
   * it can be inverted once the goal is a Prop
   * (i.e. once we provide a value for t3s)
   *)

Admitted.

(* The value stack *)
Definition stack := list value.

Inductive stack_typing : stack -> list value_type -> Prop :=
  | stack_typing_nil : stack_typing [] []
  | stack_typing_cons : forall s st t vt,
      stack_typing s st ->
      value_typing t vt ->
      stack_typing (t :: s) (vt :: st)
.

Lemma nil_stack_typing_inv : forall s, stack_typing s [] -> s = [].
Proof. intros s Hstype. inversion Hstype. by reflexivity. Qed.

Lemma cons_stack_typing_inv : forall s st t vt,
  stack_typing (t :: s) (vt :: st) ->
  stack_typing s st /\ value_typing t vt.
Proof. intros s st t tt Hstype. inversion Hstype; auto. Qed.

Lemma rcons_stack_typing_inv : forall s st t vt,
  stack_typing (s ++ [t]) (st ++ [vt]) <->
  stack_typing s st /\ value_typing t vt.
Proof.
  intros s st t tt.
  induction s.
  (* TODO this is admitted but is not used in extracted code *)
Admitted.

Lemma stack_typing_length : forall s st,
  stack_typing s st -> length s = length st.
Proof.
  intros s st Hstype.
  induction Hstype => //.
  simpl. rewrite IHHstype. reflexivity.
Qed.

Lemma rcons_stack_typing_inv' : forall s st vt,
  stack_typing s (st ++ [vt]) ->
  {s' & {t & s = s' ++ [t] /\ stack_typing s' st /\ value_typing t vt}}.
Proof.
  intros s st vt Hstype.
  (* XXX did Hlens / Hlenst end up necessary? *)
  assert (Hlens : length s = length (st ++ [vt])).
  { apply (stack_typing_length _ _ Hstype). }
  assert (Hlenst : length (st ++ [vt]) = length st + 1).
  { rewrite app_length. reflexivity. }
  rewrite Hlenst in Hlens.
  induction s as [|t s'] using rev_ind_T.
  - exfalso. rewrite plus_comm in Hlens. by discriminate Hlens.
  - exists s', t. apply rcons_stack_typing_inv in Hstype as [Hstype Hvtype].
    repeat split; by assumption.
Qed.

(* Note: the stack given to the interpreter
 * must contain the right type values *)
Fixpoint interpret_one_step
  t tf_in tf_out s
  (Htype : typing t (Tf tf_in tf_out)) (Hstype : stack_typing s tf_in)
  : {t' : term & {s' : stack & stack_typing s' tf_out}}.
Proof.
  destruct t as [| |t1 t2] eqn:Heqt.

  - (* term_const *)
    (* TODO need to consume evaluated instrs - noop instr? *)
    exists t, (s ++ [v]).
    rewrite <- Heqt in Htype.
    destruct (term_const_typing_inv t v tf_in tf_out Heqt Htype) as [tf_in' [? Htf_out]].
    subst tf_in'. rewrite Htf_out.
    apply rcons_stack_typing_inv. split.
    * by assumption.
    * by apply vt.

  - (* term_addi32 *)
    (* use Hstype to discover that the stack has at least two values on it *)
    apply (term_addi32_typing_inv) in Htype as [ts [Hts1 Hts2]].
    subst tf_in.
    assert (Hlist : ts ++ [t_i32; t_i32] = (ts ++ [t_i32]) ++ [t_i32]).
    { rewrite <- app_assoc. by reflexivity. }
    rewrite Hlist in Hstype.
    apply (rcons_stack_typing_inv' s (ts ++ [t_i32])) in Hstype.
    destruct Hstype as [s' [v1 [Hseq [Hstype Hvtype1]]]].
    apply rcons_stack_typing_inv' in Hstype.
    destruct Hstype as [s'' [v2 [Hseq1 [Hstype Hvtype2]]]].
    subst s'.

    (* now deduce t1 and t2 are both (term_const (val_i32 _)) *)
    apply value_typing_inversion_i32 in Hvtype1 as [n1].
    apply value_typing_inversion_i32 in Hvtype2 as [n2].
    exists t, (s'' ++ [val_i32 (n1 + n2)]). subst.

    apply rcons_stack_typing_inv. split.
    * by assumption.
    * by apply vt.

  - (* term_SEQ *)
    apply (term_SEQ_typing_inv (term_SEQ t1 t2) _ _ _ _ eq_refl) in Htype
    as [ts [Htype1 Htype2]].

    destruct (interpret_one_step _ _ _ s Htype1 Hstype) as [t1' [s' Hstype']].
    destruct (interpret_one_step _ _ _ s' Htype2 Hstype') as [t2' [s'' Hstype'']].

    exists (term_SEQ t1' t2'), s''.
    by apply Hstype''.
Defined.

(* Testing the interpreter *)

(* TODO replace term_SEQ with lists -- closer to wasmcert and easier to use *)
Definition term_add_2_6 : term :=
  term_SEQ
    (term_SEQ (term_const (val_i32 2)) (term_const (val_i32 6)))
    term_addi32.
Definition stack_emp : stack := [].
Definition t_in : list value_type := [].
Definition t_out : list value_type := [t_i32].

Definition term_add_2_6_typing : typing term_add_2_6 (Tf [] [t_i32]).
Proof.
  apply typing_composition with (t3s := [t_i32; t_i32]).
  - apply typing_composition with (t3s := [t_i32]).
    * apply typing_term_const. by apply vt.
    * apply typing_weaken with (ts := [t_i32]).
      apply typing_term_const. by apply vt.
  - by apply typing_term_addi32.
Qed.

Check (
  interpret_one_step
  term_add_2_6
  t_in
  t_out
  stack_emp
  term_add_2_6_typing
  stack_typing_nil
).

(* Extraction *)

From Coq Require Import Extraction.
Extraction Language Haskell.
Extraction "interpret.hs"
  interpret_one_step
  term_add_2_6
  t_in
  t_out
  stack_emp
.

(* NOTE: we don't even need to extract stack_typing_nil and term_add_2_6_typing *)

