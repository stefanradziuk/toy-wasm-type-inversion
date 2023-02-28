From mathcomp Require Import ssreflect.
From Coq Require Import Program.Equality NArith ZArith_base List Extraction Floats.
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

Inductive value_typing : value -> value_type -> Prop :=
  | val_typing_i32: forall n, value_typing (val_i32 n) t_i32
  | val_typing_f32: forall n, value_typing (val_f32 n) t_f32
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
(* XXX how to do this as sigma type? *)
Lemma value_typing_inversion_i32 : forall v,
  value_typing v t_i32 -> {n & v = val_i32 n}.
Proof.
  intros v Hvtype.
  destruct v as [n|].
  - exists n. reflexivity.
  - Fail induction Hvtype.
Admitted. (* TODO *)

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

(* TODO might need to use the type checker for this one too? *)
Lemma term_addi32_typing_inv : forall t t1s t2s,
  t = term_addi32 ->
  typing t (Tf t1s t2s) ->
  {ts & t1s = ts ++ [t_i32; t_i32] /\ t2s = ts ++ [t_i32]}.
Proof.
  intros t t1s t2s Hterm Htype.
  subst t. exists (removelast t2s); split.
Admitted.

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
  (* TODO stack type / naming *)
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
Admitted.

Lemma rcons_stack_typing_inv' : forall s st vt,
  stack_typing s (st ++ [vt]) ->
  {s' & {t & s = s' ++ [t] /\ stack_typing s' st /\ value_typing t vt}}.
Proof. (* TODO *) Admitted.

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
    apply (term_addi32_typing_inv) in Htype as [ts [Hts1 Hts2]]; last by reflexivity.
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

Recursive Extraction interpret_one_step.
