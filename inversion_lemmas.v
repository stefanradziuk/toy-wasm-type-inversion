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

(* XXX is this not provable as sigma type?
Lemma value_typing_inversion_i32 : forall v,
  value_typing v t_i32 -> {n & v = val_i32 n}.
Proof.
  intros v Hvtype.
  destruct v as [n|].
  - exists n. reflexivity.
  - Fail induction Hvtype.
Admitted. *)

Lemma term_const_typing_inv : forall t v vt t1s t2s,
  t = (term_const v) ->
  value_typing v vt ->
  typing t (Tf t1s t2s) ->
  {ts & t1s = ts /\ t2s = ts ++ [vt]}.
Proof.
  intros t v vt t1s t2s Hterm Hvtype Htype.
  subst t.
  exists t1s; split => //.
  dependent induction Htype.
  - assert (Heqvt : vt0 = vt).
    { by apply (value_typing_deterministic v _ _ H Hvtype). }
    rewrite Heqvt. reflexivity.
  - rewrite <- app_assoc; f_equal.
    by apply (IHHtype _ _ _ Hvtype); reflexivity.
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
  stack_typing (s ++ [t]) (st ++ [vt]) ->
  stack_typing s st /\ value_typing t vt.
Proof.
  intros s st t tt Hstype.
  induction s.
  (* TODO this is admitted but is not used for extraction *)
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

(* XXX no longer necessary? *)
Lemma cat_stack_typing_inv : forall s st1 st2,
  stack_typing s (st1 ++ st2) ->
  {s1 & {s2 & s = s1 ++ s2 /\ stack_typing s1 st1 /\ stack_typing s2 st2}}.
Proof. Admitted.

(* Note: the stack given to the interpreter
 * must contain the right type values *)
Definition interpret_one_step
  t tf_in tf_out s
  (Htype : typing t (Tf tf_in tf_out)) (Hstype : stack_typing s tf_in)
  : (term * stack).
Proof.
  destruct t as [| |t1 t2] eqn:teq.

  - (* term_const *)
    apply (t, s).

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
    apply (term_const (val_i32 (n1 + n2)), s'').

  - (* term_SEQ *)
    apply (term_SEQ_typing_inv (term_SEQ t1 t2) _ _ _ _ eq_refl) in Htype
    as [ts [Htype1 Htype2]].
    apply (t, s). (* TODO just doing identity for now *)
Defined.

(* Testing the interpreter *)

Definition stack_2_6 : stack := [val_i32 2; val_i32 6].
Definition t_in : list value_type := [t_i32; t_i32].
Definition t_out : list value_type := [t_i32].

Lemma stack_2_6_typing : stack_typing stack_2_6 t_in.
Proof.
  repeat apply stack_typing_cons; try apply vt.
  by apply stack_typing_nil.
Qed.

Compute (
  interpret_one_step
  term_addi32
  t_in
  t_out
  stack_2_6
  typing_term_addi32
  stack_2_6_typing
).

(* Extraction *)

From Coq Require Import Extraction.
Extraction Language Haskell.
Extraction "interpret.hs"
  interpret_one_step
  term_addi32
  t_in
  t_out
  stack_2_6
  typing_term_addi32
  stack_2_6_typing
.
