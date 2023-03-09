From SLF (* TLC *) Require Export LibCore.
From SLF (* Sep *) Require Export TLCbuffer Var Fmap Language.
(**===================== List Function for MapReduce =============================**)

Definition bloc : Type := nat.
Definition floc : Type := nat.

(* wordcount kvpair (word, times) *)
Definition wdpair : Type := int * int.

(* =================== For WordCount ==================== *)

(*-- compare kvpair --*)
Definition eqword (p1 p2: wdpair) := (fst p1) =? (fst p2).

Definition neqword (p1 p2: wdpair) := negb (eqword p1 p2).

(*--  reflexivity  --*)
Lemma eqword_refl : forall a,
  eqword a a = true.
Proof. intros. unfold eqword. simpl. apply~ Z.eqb_eq. Qed.

Lemma neqword_refl : forall a,
  neqword a a = false.
Proof. intros. unfold neqword. rewrite~ eqword_refl. Qed.


(*-- remove function is similar to filter  --*)
Lemma filter_nil : forall (a:wdpair),
  List.filter (neqword a) nil = nil.
Proof using. auto. Qed.

Lemma filter_cons : forall a x l,
  List.filter (neqword a) (x::l) = 
(If (neqword a) x then
 x :: List.filter (neqword a) l else List.filter (neqword a) l).
Proof using.
  intros. simpl. case_if; symmetry.
  apply~ If_l. apply~ If_r.
Qed.

Lemma filter_eq_self_of_mem_implies : forall l a,
  (forall x, mem x l -> ((neqword a) x)) ->
  List.filter (neqword a) l = l.
Proof using.
  induction l; introv M.
  { auto. }
  { rewrite filter_cons. case_if.
    { fequals. applys IHl. introv Mx. applys* M. }
    { false* M. } }
Qed.

Lemma mem_filter_eq : forall (x a:wdpair) (l:list wdpair),
  mem x (List.filter (neqword a) l) = 
(mem x l /\ (neqword a) x).
Proof using.
  intros. extens. induction l.
  { rewrite filter_nil. iff M (M&?); inverts M. }
  { rewrite filter_cons. case_if; rew_listx; rewrite IHl.
    { iff [M|M] N; subst*. }
    { iff M ([N|N]&K); subst*. } }
Qed.

Lemma noduplicates_filter : forall (a:wdpair) (l:list wdpair),
  noduplicates l ->
  noduplicates (List.filter (neqword a) l).
Proof using.
  introv H. induction H.
  simpl. apply noduplicates_nil.
  simpl. case_if*.
  rewrite <- app_cons_one_r.
  apply noduplicates_app.
  apply noduplicates_one.
  auto.
  intros. apply H.
  rewrite mem_filter_eq in H2.
  destruct H2 as (H2a&H2b).
  rewrite mem_cons_eq in H1.
  destruct H1. subst~.
  rewrite mem_nil_eq in H1. destruct H1.
Qed.

(* remove as filter *)
Lemma remove_as_filter : forall a l,
  remove a l = List.filter (neqword a) l.
Proof using. auto. Qed.

(* no duplicate elements before removal, and none after *)
Lemma noduplicates_remove : forall a l,
  noduplicates l ->
  noduplicates (remove a l).
Proof using.
  intros. rewrite remove_as_filter. applys* noduplicates_filter.
Qed.

Lemma mem_remove_eq : forall x a l,
  mem x (remove a l) = (mem x l /\ (neqword a x)).
Proof using. intros. applys* mem_filter_eq. Qed.


(*=========== the sequence after removal has no duplicate elements =============*)
Lemma remove_duplicates_spec : forall l l',
  l' = remove_duplicates l -> noduplicates l'.
Proof using.
  introv E.
  gen l' E. induction l; introv E; simpls.
    { subst. apply noduplicates_nil. }
    { sets_eq l'': (remove_duplicates l).
      rewrite E.
      rewrite <- app_cons_one_r.
      apply noduplicates_app.
      apply noduplicates_one.
      auto. applys noduplicates_remove. apply~ IHl.
      intros. rewrite mem_remove_eq in H0.
      destruct H0 as (H1&H2).
      rewrite mem_cons_eq in H.
  destruct H. subst x. 
  rewrite neqword_refl in H2.
  auto. rewrite mem_nil_eq in H. destruct H. }
Qed.

Lemma noduplicates_remove_duplicates : forall l,
  noduplicates (remove_duplicates l).
Proof.
  intros. applys* remove_duplicates_spec.
Qed.