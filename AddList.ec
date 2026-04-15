require import AllCore List.

(* If a list is equal to the identity at all points
      then the product of the list is the identity *)
  lemma foldr_id (a : 'a list) (ope : 'a->'a->'a) (id : 'a) :
     ope id id = id =>
     all (fun b => b = id) a => foldr ope id a = id.
  proof.
    move => eq. elim a. smt(). move => a' a h h'. simplify. rewrite h. smt(). have : a' = id. smt().
    move => h''. rewrite h''. apply eq.
  qed.

  lemma foldr_id_nth_sub (a : 'a list) (ope : 'a->'a->'a) (id : 'a) :
     (forall a, ope a id = a) =>
     (forall a b, ope a b = ope b a) => 
     forall i, 0 <= i =>  all (fun b => b = id) (rem (nth id a i) a) => foldr ope id a = nth id a i.
  proof.
  move => eq com. elim a. smt(). move => a' a h i hi h'. simplify. case(i = 0) => h''. rewrite foldr_id. trivial. smt().
    smt(). smt(). rewrite (h (i -1)). smt(). smt(@List). have : a' = id.  smt(@List). move => h'''. rewrite h'''. smt().
qed.

  lemma foldr_id_nth (a : 'a list) (ope : 'a->'a->'a) (id : 'a) i :
     (forall a, ope a id = a) =>
     (forall a b, ope a b = ope b a) => 
     all (fun b => b = id) (rem (nth id a i) a) => foldr ope id a = nth id a i.
  proof.
    case (i < 0). move => hi eq com all. rewrite nth_neg; trivial. rewrite foldr_id; trivial.
    smt(). smt(@List). smt(foldr_id_nth_sub).
qed.

  lemma foldr_ann_in (a : 'a list) (ope : 'a->'a->'a) (id b : 'a) :
     (forall a, ope a id = id) =>
     (forall a b, ope a b = ope b a) =>
     id \in a => foldr ope b a = id.
  proof.
  move => ann com. elim a. smt(@List). move => x l ind_hyp h. simplify. case (x = id) => g.
  rewrite g. rewrite com. apply ann. rewrite ind_hyp. smt(). apply ann.
qed.

  lemma mkseq_index (f : int -> 'a) (i j : int) : 0 <= i < j => index (f i) (mkseq f j) <= i.
  proof.  
    move => h. have : f i = nth witness (mkseq f j) i. rewrite nth_mkseq. smt(). trivial. move => h'. rewrite h'. smt(@List).
  qed.
  
  (* If predicate holds for every element in a list then it is true for the element at every index *)
  lemma all_nth p x0 (l : 'a list): 
    all p l <=> (forall i, 0 <= i < size l => p (nth x0 l i)).
      proof. elim l. smt(). move => x l h. split. 
        move => h'. elim h'. move => h' h'' i. case (i = 0). move => h'''. smt().
          move => h'''. move => h''''. rewrite (h) in h''. rewrite h'''. simplify.
          apply h''. smt().
        move => h'. simplify. split. apply (h' 0). smt(@List). apply h. move => i h''.
        have : p (nth x0 (x :: l) (i+1)). apply h'. smt(). smt().
    qed.

  lemma foldr_rcons zero (add : 't -> 't -> 't) l a :
     (forall a b c, add (add a b) c = add a (add b c)) =>
     (forall a b, add a b = add b a) =>
      foldr add zero (rcons l a) = add a (foldr add zero l).
  proof.
    move => ass com. elim l. simplify. trivial. move => x l ind. simplify. smt().
  qed.

  lemma foldr_cat (mul : 't -> 't-> 't) e a b :
    (forall b, mul e b = b) =>
    (forall a b c, mul (mul a b) c = mul a (mul b c)) =>  
    foldr mul e (a ++ b) = mul (foldr mul e a)
    (foldr mul e b).
  proof.
    elim a. simplify. smt(). move => x h l id ass. simplify. rewrite l. smt().  smt(). rewrite ass. trivial.
  qed.

  lemma eq_foldr_trunc zero (add : 't -> 't -> 't) m m' :
    (forall (b : 't), add zero b = b) =>
    (forall a b c, add (add a b) c = add a (add b c)) =>
    (forall a b, add a b = add b a) =>
    (forall i, 0<= i < max (size m)(size m') => nth zero m i = nth zero m' i) =>
    foldr add zero m =  foldr add zero m'.
  proof.
    move => id ass comm h. case (size m <= size m'); move => h'. rewrite -(cat_take_drop (size m) m'). rewrite foldr_cat; trivial.
    rewrite (foldr_id (drop (size m) m')). smt(). apply (all_nth _ zero). move => i g. simplify.
    rewrite nth_drop. smt(@List). smt(@List). rewrite -h. smt(@List). smt(@List). rewrite comm. rewrite id.
    apply eq_foldr; trivial. apply (eq_from_nth zero). smt(@List). move => i g. smt(@List).
    (* case 2 *)
    rewrite -(cat_take_drop (size m') m). rewrite foldr_cat; trivial. rewrite (foldr_id (drop (size m') m)). smt().
    apply (all_nth _ zero). move => i g. simplify. rewrite nth_drop. smt(@List). smt(@List). rewrite h. smt(@List).
    smt(@List). rewrite comm. rewrite id. apply eq_foldr; trivial. apply (eq_from_nth zero). smt(@List). move => i g. smt(@List).
  qed.    

  lemma foldr_const (add : 't -> 't -> 't) (a : 't list) :
      (forall a b, add a b = add b a) =>
      (forall a b c, add (add a b) c = add a (add b c)) =>
      forall (x b : 't), foldr add (add b x) a = add x (foldr add b a).
  proof.
    elim a. move => comm ass x b. simplify. smt(). move => x a ind_hyp comm ass x0 b0. simplify. rewrite ind_hyp; smt().
  qed.
      
  lemma foldr_foldl_eq (add : 't -> 't -> 't)(a : 't list) :
     (forall a b, add a b = add b a) =>
     (forall a b c, add (add a b) c = add a (add b c)) =>
     forall b, foldr add b a =  foldl add b a.
  proof.
    elim a. simplify. trivial. move => x l ind_hyp comm ass. move => b. simplify. rewrite -ind_hyp; trivial.
    rewrite foldr_const; trivial.
  qed.
      
  lemma foldr_add_distr_sub (add : 't -> 't -> 't)(zero : 't)(a: 't list) :
      (forall h, add zero h = h) =>
      (forall a b, add a b = add b a) =>
      (forall a b c, add (add a b) c = add a (add b c)) =>
    forall b, size a <= size b =>
    add (foldr add zero a) (foldr add zero b) =
    foldr add zero (mkseq (fun (i : int) => add (nth zero a i) (nth zero b i)) (max (size a) (size b))).  
   proof.
    (* base case *)   
   elim a. move => id com ass h b. simplify.   (* inductive case *)
   rewrite id. apply eq_foldr; trivial.
    apply (eq_from_nth zero). smt(@List). move => i h''. rewrite nth_mkseq. smt(). simplify. smt().
   (* inductive case *)
   move => x a ind_hyp id comm ass b. elim b. smt(@List). move => x0 b ind_hyp2 h. simplify.
   have : forall (a b c d : 't), add (add a b) (add c d) = add (add a c) (add b d). smt().
   move => g. rewrite g. rewrite ind_hyp; trivial. smt(). 
   (* simplify orders *)
   have :  max (size a) (size b) = size b. smt(@Int @List).
   move => h'. rewrite h'. have : max (1 + size a)(1+ size b) = size b + 1. smt(@Int @List). move => h''. rewrite h''.
   (* *)
     rewrite mkseqSr. smt(@List). simplify. have : forall a b b' n, (forall i, 0 <= i => b i = b' i) =>
     add a (foldr add zero (mkseq b n)) = add a (foldr add zero (mkseq b' n)). smt(@List). move => g'. apply g'.
     move => i g''. move => @/(\o). simplify. smt(@Int).
  qed.

  lemma foldr_eq_partL (mul : 't -> 't -> 't) e a b  :
   (forall (b0 : 't), mul e b0 = b0) =>
   (forall a b, mul a b = mul b a) =>   
   (forall (a0 b0 c : 't), mul (mul a0 b0) c = mul a0 (mul b0 c)) =>
    size a <= size b =>
    a = take (size a) b =>
    all (fun a => a = e) (drop (size a) b) =>
    foldr mul e a = foldr mul e b.
  proof.
    move => id comm ass h h' h''. rewrite -(cat_take_drop (size a) b). rewrite foldr_cat; trivial. rewrite -h'.
    rewrite (foldr_id (drop (size a) b)). smt(). trivial. smt().
  qed.

  lemma foldr_eq_partR (mul : 't -> 't -> 't) e a b  :
   (forall (a b : 't), a = b <=> b = a) =>
   (forall (b0 : 't), mul e b0 = b0) =>
   (forall a b, mul a b = mul b a) =>   
   (forall (a0 b0 c : 't), mul (mul a0 b0) c = mul a0 (mul b0 c)) =>
   size b <= size a =>
    b = take (size b) a =>
    all (fun a => a = e) (drop (size b) a) =>
    foldr mul e a = foldr mul e b.
  proof.
    move => eq id comm ass h h' h''. rewrite eq. apply foldr_eq_partL; trivial.
  qed.
  
  lemma mkseq_nth_mkseq (a : 'a)(c : 'c)(f : int -> 'a)(f' : int -> 'b)
      (g : 'a -> 'b -> 'c)(s s' : int) :
      0 <= s => s <= s' =>
      mkseq (fun (i : int) => g (nth a (mkseq f s') i) (f' i)) s =
      mkseq (fun (i : int) => g (f i) (f' i)) s.
  proof.
    move => h h'. apply (eq_from_nth c). smt(@List). move => i h'''. rewrite nth_mkseq. smt(@List).
    rewrite nth_mkseq. smt(@List). simplify. rewrite nth_mkseq. rewrite size_mkseq in h'''.
    split. smt(@List). move => h''''. smt(). trivial.
  qed.

  lemma dis_neg (add : 't -> 't -> 't) (neg : 't -> 't) zero m:
    (neg zero = zero) =>
    (forall x y, neg (add x y) = add (neg x) (neg y)) =>
    neg (foldr add zero m) =
    foldr add zero ((map neg) m).
  proof.
    elim m. simplify. trivial.
    (* induction *)
    move => x l ind_hyp neg_zero dist. simplify. rewrite -ind_hyp; trivial. smt().
  qed.

  lemma dis_mul_add (add : 't -> 't -> 't)(mul : 't -> 't -> 't) zero m e:
      (forall b, mul zero b = zero) =>
      (forall a b c, mul (add a b) c = add (mul a c) (mul b c)) =>
      mul (foldr add zero m) e = foldr add zero (map (fun x => mul x e) m).
  proof.
    elim m. move => ann. simplify. smt().
    (* induction *)
    move => x l ind_hyp ann dis. simplify. rewrite -ind_hyp; trivial. smt().
  qed.


lemma rem_nth ['a] (a:'a) (i : 'a) l :
    forall j, 0 <= j => nth a (rem i l) j = nth a l (if j < index i l then j else j + 1).
    elim l. smt().
    move => x l hind j hj. simplify. rewrite index_cons. case (i=x) => h. rewrite h. simplify. have : !(j < 0). smt().
      move => h'. rewrite h'. simplify. have : j +1 <> 0. smt(). move => g. rewrite g. simplify.  trivial.
      have : x<>i. smt(). move => h'. rewrite h'. simplify. case (j < index i l + 1) => g. case (j=0) => g'. trivial.
    rewrite hind. smt(). smt(). have : j <> 0. smt(@List). move => g'. rewrite g'. have : j +1 <> 0. smt(@List).
    move => g''. rewrite g''. simplify. rewrite hind. smt(). smt().
  qed.

  lemma foldr_id_nth_mkseq_sub (ope : 'a->'a->'a) (id : 'a) i j (f : int -> 'a) :
     (forall a, ope a id = a) =>
     (forall a b, ope a b = ope b a) =>
     (forall (a b c : 'a), ope (ope a b) c = ope a (ope b c)) =>
     0 <= i =>
     0 < j =>
     all (fun b => b = id) (mkseq f i) =>
     all (fun b => b = id) (mkseq (fun x => f (i + (1+ x))) (j-1)) =>
     foldr ope id (mkseq f (i+j)) = f i.
  proof.
    move => eq com ass hi hj h h'. rewrite (mkseq_add _ i j). smt(). smt(). rewrite foldr_cat; trivial. smt().
    rewrite foldr_id; trivial. smt(). rewrite (com id _). rewrite eq. pose q := j -1.  have : j = q + 1. smt(@Int).
    move => g'. rewrite g'. rewrite mkseqSr. smt(). simplify. rewrite foldr_id; trivial. smt(). smt().
  qed.

  lemma foldr_id_nth_mkseq (ope : 'a->'a->'a) (id : 'a) j i (f : int -> 'a) :
     (forall a, ope a id = a) =>
     (forall a b, ope a b = ope b a) =>
     (forall (a b c : 'a), ope (ope a b) c = ope a (ope b c)) =>
     0 <= i && i < j =>
     all (fun b => b = id) (mkseq f i) =>
     all (fun b => b = id) (mkseq (fun x => f (x + i + 1)) (j-i-1)) =>
     foldr ope id (mkseq f j) = f i.
  proof.
    move => eq com ass hj h h'. pose q := j - i. have : j = i + q. smt(). move => g. rewrite g.
    apply foldr_id_nth_mkseq_sub; trivial. smt(). smt(). smt().
  qed.

  lemma countU (p q : 'a -> bool) (xs : 'a list): count (predU p q) xs = count p xs + count q xs - count (predI p q) xs.
  proof.  
    elim xs. simplify. trivial. move => x l. smt().
  qed.

  lemma countI (p q : 'a -> bool) (xs : 'a list): count (predI p q) xs = count p xs + count q xs - count (predU p q) xs.
  proof.
    rewrite countU. smt().
  qed.

  lemma countC p (s : 'a list):
    count (predC p) s = size s -  count p s.
  proof. elim: s; smt(). qed.

lemma insert_map (f : 'a -> 'b) (j : 'a) js i :
    insert (f j) (map f js) i = map f (insert j js i).
proof.
  smt(@List).
qed.

(*
lemma insert_rem_sub : forall (s : int), 0 <= s => forall (js : 'a list) j, size js = s =>
    uniq js => j \in js => js = insert j (rem j js) (index j js).
proof.
  apply intind. simplify. smt(@List).  move => i hi ind_hyp. simplify.
  move => js j size_js uniq_js j_in_js.  
qed. *)
    

lemma nth_insert_gen ['a] (a:'a) (i : 'a) l w j : 0 <= w => w <= size l => w <> j =>
    nth a (insert i l w) j = nth a l (if j < w then j else j -1).
  proof.
    move => h0 h1 h2. rewrite nth_cat. rewrite size_take; trivial. case ( w < size l) => h'.
    (* case 1 *) case (j < w) => h''. rewrite nth_take; trivial. have : (j - w <> 0).
    smt(). move => h. rewrite h. simplify. rewrite nth_drop; trivial. smt(). congr.
    smt(). 
    (* case 2 *)
    case (j < size l) => h''. case ( j < w) => h'''. rewrite nth_take; trivial.
    smt(). have : j - size l <> 0. smt(@List). move => g'. rewrite g'. 
    simplify. rewrite nth_drop; trivial. smt(). congr. smt(). 
  qed.

lemma insert_rem (js : 'a list) j : uniq js => j \in js =>
    js = insert j (rem j js) (index j js).
proof.
  move => h h0. apply (eq_from_nth witness). smt(@List).
  move => i hi. case (i = (index j js)) => g. subst. rewrite nth_insert. smt(@List). smt(@List).
  rewrite nth_insert_gen. smt(@List). smt(@List). smt(@List). rewrite rem_nth. smt(@List).
  case (i < index j js) => h'. smt(). smt().
qed.
    
lemma foldr_add_distr_f (f f'  : int -> 'a)(add : 'a-> 'a -> 'a)(zero : 'a) :
    (forall (a b c : 'a), add (add a b) c = add a (add b c)) =>
    (forall (a b : 'a), add a b = add b a) =>
    (forall (a : 'a), a = add a zero) =>
    forall i, 0 <= i =>
    foldr add zero (mkseq (fun (i0 : int) => add (f i0) (f' i0)) i)
    = add (foldr add zero (mkseq f i)) (foldr add zero (mkseq f' i)).
proof.
  move => assoc comm add0. apply intind. simplify. rewrite !mkseq0. simplify. apply add0.
  simplify. move => i hi ind_hyp. rewrite mkseqS. smt(). rewrite foldr_rcons; trivial.
  rewrite ind_hyp. rewrite mkseqS. smt(). rewrite mkseqS. smt(). rewrite !foldr_rcons; trivial. simplify.
  smt(). 
qed.

(* Rearrange a double loop *)
lemma double_loop_rearr (f : int -> 'a)(add : 'a-> 'a -> 'a)(zero : 'a)(exp : 'a -> int -> 'a) :
    (forall (a : 'a) i, 0 <= i => exp a (i+1) = add a (exp a i)) =>
    (forall (a : 'a) i, i =1 => exp a i = a) =>
    (forall (a : 'a), exp a 0 = zero) =>
   (forall (a b c : 'a), add (add a b) c = add a (add b c)) =>
   (forall (a b : 'a), add a b = add b a) =>
   (forall (a : 'a), a = add a zero) =>
    forall n, 0 <= n =>
  foldr add zero (mkseq (fun (i : int) =>
    foldr add zero (mkseq (fun (j : int) => f (i + j)) (n- i))) n) =
    foldr add zero (mkseq (fun (i : int) => exp (f i) (i + 1)) n).
proof.
  move => expS exp1 exp0 trans comm addr. apply intind. simplify. rewrite !mkseq0. trivial.
  simplify. move => i hi ind_hyp. rewrite eq_sym. rewrite mkseqS. smt(). rewrite foldr_rcons; trivial. simplify.
  rewrite -ind_hyp. rewrite mkseqS. smt(). rewrite foldr_rcons; trivial. simplify.
  have : exp (f i) (i + 1) = add (f i) (foldr add zero (mkseq (fun j => f i) (i))). rewrite expS. trivial. congr.
  clear ind_hyp. have : forall j, 0 <= j => exp (f i) j = foldr add zero (mkseq (fun (_ : int) => f i) j).
  apply intind. simplify. rewrite mkseq0. simplify. apply exp0. simplify. move => i0 ghi0 ind.
  rewrite expS. smt(). rewrite ind. rewrite mkseqS. smt(). rewrite foldr_rcons; trivial. move => g. apply g. smt().
  move => j. rewrite j. rewrite trans. rewrite -foldr_add_distr_f; trivial. congr.
  have : i + 1 -i = 1. smt(). move => g. rewrite g. rewrite mkseq1. simplify. smt().
  congr. apply (eq_from_nth zero). smt(@List). move => i0 hi0. rewrite !nth_mkseq. smt(@List). smt(@List).
  simplify.  have : i + 1 -i0 = i -i0 +1. smt(). move => g''. rewrite g''. rewrite mkseqS. smt(@List). simplify.
  rewrite foldr_rcons; trivial. congr. smt().
qed.

lemma sumz_cat i a b c d :
i < sumz (a ++ b) =>
sumz a <= sumz c =>
sumz b <= sumz d =>
i < sumz (c ++ d).
proof.
  move =>@/sumz. rewrite foldr_cat. smt(@Int). smt(@Int).
  rewrite foldr_cat. smt(@Int). smt(@Int). move => h h' h''.
  have : forall (a b c d : int), i < a+b => a <=c => b<=d => i < c+d.
  smt(@Int). move => q. apply (q _ _ _ _ h h' h'').
qed.

lemma gtk_ge0 a :
    all ((<=) 0) a =>
    0 <= sumz a.
proof.
  smt(@List).
qed.

lemma gtk_sumz a k :
    all ((<=) 0) a =>
    (exists s, mem a s /\ k < s) =>
      k < sumz a.
proof.
elim a => h. smt(). move => @/sumz l ind_hyp all_ge0 h'. simplify.
  have : (exists (s : int), (s \in l) /\ k < s) => k < foldr Int.(+) 0 l. apply ind_hyp. smt(@List). move => h''.
  elim h' => s sh. case (s = h) => h'''. subst. have : 0 <= foldr Int.(+) 0 l => k < h + (foldr Int.(+) 0 l). smt(@Int).
  move => g. apply g. apply gtk_ge0. smt(). have : k < foldr Int.(+) 0 l => k < h + (foldr Int.(+) 0 l). smt(@Int @List).
  move => g. apply g. apply ind_hyp. smt(@List). smt(@List).
qed.
