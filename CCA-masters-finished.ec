(*** Import the theories (lemmas, operators, ...) we use throughout the proof ***)
require import AllCore DBool Distr FSet RealSeries List StdOrder.
require (*  *) FelTactic.
(*   *) import RealOrder.  

(*** Remove the SMT prover Alt-Ergo from the list of available provers due to a bug ***)
prover [-"Alt-Ergo"]. 

(*** Introduce the types we use throughout the proof ***)
type X, Y, K, S, W.
type Y_, K_, S_.

(*** Define the sets xs, ls, ys and ws  ***)
op xs : { X fset | is_full (duniform (elems xs)) /\ is_uniform (duniform (elems xs)) /\ is_lossless (duniform (elems xs)) } as xs_ful.
lemma xs_luf : is_full (duniform (elems xs)) /\ is_uniform (duniform (elems xs)) /\ is_lossless (duniform (elems xs)) by []. 

op ls : { X fset | ls < xs /\ is_uniform (duniform (elems ls)) /\ is_lossless (duniform (elems ls)) } as ls_ful.
lemma ls_lu : is_uniform (duniform (elems ls)) /\ is_lossless (duniform (elems ls)) by smt. 

op ws : { W fset | is_full (duniform (elems ws)) /\ is_uniform (duniform (elems ws)) /\ is_lossless (duniform (elems ws)) } as ws_ful. 
lemma ws_luf : is_full (duniform (elems ws)) /\ is_uniform (duniform (elems ws)) /\ is_lossless (duniform (elems ws)) by smt. 

op ys : { Y fset | is_lossless (duniform (elems ys)) /\ is_full (duniform (elems ys)) /\ is_uniform (duniform (elems ys))} as ys_lfu. 
lemma ys_ful : is_lossless (duniform (elems ys)) /\ is_full (duniform (elems ys)) /\ is_uniform (duniform (elems ys)) by [].  

(*** Lemmas provided as a check that the subset ls behaves the way we want it to, 
     i.e. as a proper subset of xs ***)
lemma subset : ls < xs by []. 

lemma memX : forall (x:X), x \in xs. 
proof. 
move => x. 
have : is_full (duniform (elems xs)) by smt(xs_luf). 
move => ?; smt. 
qed. 

lemma mem x : x \in xs => x \in ls \/ x \in xs `\` ls by smt.   

lemma sub1 : forall (x:X), x \in ls => x \in xs by smt.  

lemma sub2 : exists x, x \in xs /\ !(x \in ls) by smt(subset).  

lemma sub3 : xs `\` ls <> fset0 by smt.

lemma sub4 x : x \in xs `\` ls <=> !(x \in ls) by smt.   

(*** Operators and axioms allowing us to properly work with witnesses for x in ls ***)
op wfun  : W -> X.
axiom uniwit (ls:X fset, x:X) : x \in ls => exists w, wfun w = x.  

op iswit x   : W -> bool = fun (w:W) => wfun w = x.

axiom wit_ll x : is_lossless (duniform (elems (filter (iswit x) ws))).

(*** Define a module with procedures sampling elements from xs, xs `\` ls, ls and ys. ***)
module Sampling  = {
  proc fromX() : X = {
    var x;
    x <$ duniform (elems xs);
    return x;
  }

  proc fromL() : X*W = {
    var x,w;
    x <$ duniform (elems ls);
    w <$ duniform (elems (filter (iswit x) ws));
    return (x,w);
  }

  proc fromXnotL() : X = {
    var x;
    x <$ duniform (elems (xs `\` ls));
    return x;
  }

  proc fromY() : Y = {
    var y;
    y <$ duniform (elems ys);
    return y;
  }
}.

(*** A check whether the sampling procedures behave as we want the to ***)
lemma mem1 : forall v, v \in (xs `\` ls) <=> (v \in xs) /\ !(v \in ls)
by smt. 

lemma mem2 : forall (x:X), x\in xs => x \in (xs `\` ls) <=> !(x \in ls).
proof. 
move => x H; split. 
smt.    
smt. 
qed.     

lemma mem3 : forall (x:X), x \in ls <=> !(x \in (xs `\` ls)).
proof. 
move => x; smt.  
qed. 

lemma mem4 : forall (x:X), x \in ls \/ x \in (xs `\` ls) by smt. 

lemma test1 &m : phoare[Sampling.fromX : true ==> mem xs res] = 1%r.
proof.  
proc; auto; smt. 
qed. 

lemma test2  &m : phoare[Sampling.fromL : true ==> mem xs res.`1] = 1%r.
proof. 
proc; auto; progress. smt. 
smt. smt. 
qed. 

lemma test3  : phoare[Sampling.fromL : true ==> ! (mem (xs `\` ls) res.`1)] = 1%r.
proof. 
proc; auto; progress. smt. smt. rewrite -mem3; smt. 
qed.

lemma test4  : phoare[Sampling.fromXnotL : true ==> ! (mem ls res)] = 1%r.
proof. 
proc; auto; progress. smt. rewrite -(mem2). smt. smt. 
qed.

(*** Abstract operators for hashing and projecting in the "regular" hash proof system ***)
op alpha : K -> S.
op hash  : K * X -> Y. 
op proj  : S * X * W -> Y.

(*** Abstract operators for hashing and projecting in the extended hash proof system ***)
op alpha_ : K_ -> S_.
op hash_  : K_ * X * Y -> Y_.
op proj_  : S_ * X * Y * W -> Y_.

(*** Define the projective properties of the hash families ***)
axiom projective x w : forall (k:K), x \in ls => w \in filter (iswit x) ws =>  hash(k,x) = proj (alpha k, x, w).
lemma projref k x w : hash(k,x) = proj (alpha k, x, w) <=> proj (alpha k, x, w) = hash(k,x) by smt(projective). 
axiom projective_ x k_ e w : x \in ls => w \in filter (iswit x) ws => hash_ (k_, x,e) = proj_ (alpha_ k_, x,e, w).  

(*** Equip the key types K and K_ with full, lossless, uniform distributions ***)
op dK : { K distr | is_lossless dK /\ is_full dK /\ is_uniform dK /\ is_funiform dK } as
        dK_llfuni.
lemma dK_llfu : is_lossless dK /\ is_full dK /\ is_uniform dK /\ is_funiform dK by []. 
lemma dK_weight : weight dK = 1%r by smt(dK_llfu). 

op dK_ : { K_ distr | is_lossless dK_ /\ is_full dK_ /\ is_uniform dK_ /\ is_funiform dK_ } as
        dK_llfuni_.
lemma dK_llfu2 : is_lossless dK_ /\ is_full dK_ /\ is_uniform dK_ /\ is_funiform dK_ by []. 
lemma dK2_weight : weight dK_ = 1%r by smt(dK_llfu2). 

(*** The "regular" hash proof system ***)
module HPS = {
  proc kg() : K = {
    var k;
    k <$ dK;
    return k;
  }

  proc seval(k:K) : S = {
    var s;
    s <- alpha k;
    return s;
  }

  proc priveval(k, x) : Y = {
    var y;
    y <- hash(k,x);
    return y;
  }
  
   proc pubeval(s, x, w) : Y = {
    var y;
    y <- proj(s,x,w);
    return y;
  } 
}. 

(*** The extended hash proof system ***)
module HPS_Ext = {
  proc kg() : K_ = {
    var k_;
    k_ <$ dK_;
    return k_;
  }

  proc seval(k_) : S_ = {
    var s_;
    s_ <- alpha_ k_;
    return s_;
  }

  proc priveval(k_, x_, e) : Y_ = {
    var y_;
    y_ <- hash_ (k_ ,x_, e);
    return y_;
  }

  proc pubeval(s_, x_, e, w) : Y_ = {
    var y_;
    y_ <- proj_( s_ ,x_,e, w);
    return y_;
  }
}.

(*** Define types for the keys, plaintexts and ciphertexts we use in the encryption scheme ***)
type pkey       = S * S_.
type skey       = K * K_.
type plaintext  = Y.
type ciphertext = X * Y * Y_. 

(*** A general module type for encryption schemes ***)
module type Scheme = {
  proc keygen()                       : pkey * skey
  proc encrypt(pk:pkey, m:plaintext)  : ciphertext
  proc decrypt(sk:skey, c:ciphertext) : plaintext option
}.

(*** Operators and axioms allowing us to add and subtract elements of type Y, by treating them as integers ***)
op toint : Y   -> int.
op toY   : int -> Y.
axiom y1 : forall (y:Y), toY (toint y) = y.
axiom y2 : forall (x:int), toint (toY x) = x. 

(*** The encryption scheme ***)
module Genscheme : Scheme = {
  proc keygen() : pkey * skey = {
    var k, k_, s, s_, pk, sk;
    k  <- HPS.kg(); 
    k_ <- HPS_Ext.kg();
    s  <- HPS.seval(k); 
    s_ <- HPS_Ext.seval(k_);
    pk <- (s, s_);
    sk <- (k, k_);
    return (pk, sk);
  }

  proc encrypt(pk:pkey, m) : ciphertext = {
    var x, w, y, e, y_, c;
    (x,w) <- Sampling.fromL();
    y     <- HPS.pubeval(pk.`1,x,w);
    e     <- toY (toint m + toint y);
    y_    <- HPS_Ext.pubeval(pk.`2, x, e, w);
    c     <- (x, e, y_);
    return c;
  }

  proc decrypt(sk:skey, c:ciphertext) : plaintext option = {
    var y, y_', m;
    y_' <- HPS_Ext.priveval(sk.`2, c.`1, c.`2);
    if ( c.`3 = y_') {
      y <- HPS.priveval(sk.`1,c.`1);
      m <- Some (toY (toint c.`2 - toint y));
    } else {
      m <- None;
    }
    return m;
  }
}.

(*** Proof of correctness for the encryption scheme ***)
module Genschemecorrect = {
  proc main(m:plaintext) : bool = {
    var pk  : pkey;
    var sk  : skey;
    var c   : ciphertext;
    var m'  : plaintext option;

    (pk,sk) <- Genscheme.keygen();
      c     <- Genscheme.encrypt(pk, m);
      m'    <- Genscheme.decrypt(sk, c);

    return (m' = Some m);
  }
}.

lemma Genschemecorrectness &m : 
    hoare[Genschemecorrect.main : true ==> res].
proof.
  proc; inline*; auto. 
  progress. smt.
  have -> : proj (alpha k0, x00, w00) = hash(k0, x00) by smt. smt(y1 y2). 
qed.

(*** Maximum number of queries to the decryption oracle ***)
const qD : int.
axiom qDpos : 0 < qD.

(*** A module type that will serve as the decryption oracle in the CCA attack ***)
module type CCAoracle = {
  proc decrypt(c:ciphertext) : plaintext option
}. 

(*** An abstract CCA adversary with access to the decryption oracle
      in every stage of the attack ***)
module type CCAadv (O:CCAoracle) = {
  proc choose(pk:pkey)     : plaintext * plaintext {O.decrypt}
  proc guess(c:ciphertext) : bool {O.decrypt}
}.

(*** A general CCA attack ***)
module CCA (S:Scheme, A:CCAadv) = {
  var log   : ciphertext list
  var cstar : ciphertext option
  var sk    : skey

  module O = {
    proc decrypt(c:ciphertext) : plaintext option = {
      var m : plaintext option;
      if (size log < qD && (Some c <> cstar)) {
        log <- c :: log;
        m   <- S.decrypt(sk, c);
      }
      else m <- None;
      return m;
    }
  }

  module A = A(O)

  proc main() : bool = {
    var pk, m0, m1, c, b, b';
      log    <- [];
     cstar   <- None;
    (pk, sk) <- S.keygen();
    (m0, m1) <- A.choose(pk);
       b     <$ {0,1};
       c     <- S.encrypt(pk, b?m1:m0);
     cstar   <- Some c;
       b'    <- A.guess(c);
    return (b = b');
  }
}.

(*** Smoothness adversary guessing that y is either a 
        correct hash value or randomly chosen ***)
(*** NOTE: We perform a reduction from a CCA adversary to a smoothness 
     adversary further down, in the security section ***)
module type SmoothAdversary = {
  proc guess(x:X, s:S, (* s_:S_,*) y:Y) : bool
}.

(*** SMP adversary, we make a reduction from a CCA adversary to a 
  SMP adversary in the security section ***)
module type SMPadversary = {
  proc guess(x:X) : bool
}.

module SMP1(A:SMPadversary) = {
  proc main() : bool = {
    var b, x, w;
    (x,w) <- Sampling.fromL();
      b   <- A.guess(x);
    return b;
  }
}.

module SMP0(A:SMPadversary) = {
  proc main() : bool = {
    var x, b;
    x <- Sampling.fromXnotL();
    b <- A.guess(x);
    return b;
  }
}.

(*** Start of the security proof ***)
section Security.

(*** A module of type CCAadv without access to the CCA attack module ***)
declare module A : CCAadv{CCA}.
(*** Making sure that the procedures of the adversary terminate,
     provided the decryption oracle terminates ***)
axiom Ag_ll : forall (O <: CCAoracle{A}), islossless O.decrypt => islossless A(O).guess. 
axiom Ac_ll : forall (O <: CCAoracle{A}), islossless O.decrypt => islossless A(O).choose. 

(*** Proofs that the procedures of the CCA module are lossless ***)
local lemma CCA_O_ll : islossless CCA(Genscheme,A).O.decrypt. 
proof.
proc; inline*. 
if => //; auto. 
qed. 

local lemma CCA_ll : islossless CCA(Genscheme,A).main.
proof.
proc; inline*. call(_:true).
 + by apply Ag_ll.  
proc*. inline*. sp; skip; smt. 
auto. call(_:true). 
 + by apply Ac_ll. 
proc; inline*. 
if => //. auto. wp. skip. smt. 
auto. progress. smt(dK_weight). smt(dK2_weight). smt(@DBool). smt(ls_ful). smt. 
qed. 

(*** A simulator, perfectly simulating the original attack ***)
local module Game1(A:CCAadv) = {
  var log   : ciphertext list
  var cstar : ciphertext option
  var sk    : skey

  module O = {
    proc decrypt(c:ciphertext) : plaintext option = {
      var m : plaintext option;
      var y_', y;
      if (size log < qD && (Some c <> cstar)) {
        log <- c :: log;
        y_' <- HPS_Ext.priveval(sk.`2, c.`1, c.`2); 
        if (y_' = c.`3) {
          y <- HPS.priveval(sk.`1, c.`1);
          m <- Some (toY (toint c.`2 - toint y));
        } else m <- None;
      }
      else m <- None;
      return m;
    }
  }


  module A = A(O)

  proc main() : bool = {
    var xstar, w, m0, m1, b, b', ystar, y_', estar, c, pk;
      log      <- [];
     cstar     <- None;
    (pk, sk)   <- Genscheme.keygen();
    (xstar, w) <- Sampling.fromL();
    (m0, m1)   <- A.choose(pk);
       b       <$ {0,1};
     ystar     <- HPS.priveval(sk.`1, xstar);
     estar     <- toY (toint (b?m1:m0) + toint ystar);
       y_'     <- HPS_Ext.priveval(sk.`2, xstar, estar);
       c       <- (xstar, estar, y_');
     cstar     <- Some c;
       b'      <- A.guess(c);
    return (b = b');
  }
}.

(*** Proofs that the procedures of the simulator Game1 are lossless ***)
local lemma Game1_O_ll : islossless Game1(A).O.decrypt. 
proof.
 proc; inline*. 
auto; smt.  
qed. 

local lemma Game1_main_ll : islossless Game1(A).main. 
proof. 
proc; inline*. 
call(_:true). 
  + by apply Ag_ll. 
proc; inline*. 
auto; smt. 
auto. call(_:true). 
  + by apply Ac_ll. 
proc; inline*. 
auto; smt. 
auto. progress. smt(dK_weight). smt(dK2_weight).  smt(ls_ful). smt(wit_ll). smt(@DBool).  
qed. 

(*** Proof that the simulator perfectly simulates the original attack ***)
local equiv CCA_Game1_main : CCA(Genscheme,A).main ~ Game1(A).main : 
  ={glob A} ==> ={res}.
proof. 
proc; inline*.
call (_: CCA.log{1} = Game1.log{2} /\ CCA.sk{1} = Game1.sk{2} /\ CCA.cstar{1} = Game1.cstar{2}). 
proc; inline*.
if => //. sp 8 6.  if => //. smt. wp; skip; first smt. wp; skip; first smt. 
wp;skip;first smt. 
swap{1} [20..22] -4.   
wp. rnd. 
call (_: CCA.log{1} = Game1.log{2} /\ CCA.sk{1} = Game1.sk{2} /\ CCA.cstar{1} = Game1.cstar{2}).
proc; inline*.
if => //=. sp 8 6. if => //=. smt. 
wp. skip. smt. wp. skip. smt. wp; skip. smt. 
wp. do 2! rnd. wp. sp. rnd; wp; rnd; skip. 
move => ? ? ? ? ?; split; first smt.  move => ?; split; first smt. 
move => ? ? ?. split; first smt. move => ? ? ? ?. split; first smt. 
move => ? ? ?. split; first smt. move => ? ? ?. split; first smt. 
move => ?. split; first done. move => ?. split. smt. 
move => ? ? ? ? ? ? ? ? ? ?. split. by exact/H13. 
move => ? ? ? ? ? ? ?. split. split.  
have -> : c_L = (x0L, e_L, proj_ (pk_L.`2, x0L, e_L, w0L)) by smt. 
have -> : c_R = (x0L, estar_R, hash_ (sk_R.`2,x0L, estar_R)) by smt.  
have -> : estar_R = e_L. have -> :  estar_R =  toY (toint (if bL then result_R.`2 else result_R.`1) + toint (hash (sk_R.`1, x0L))) by smt. 
have -> : e_L = toY (toint (if bL then result_L.`2 else result_L.`1) + toint (proj (pk_L.`1, x0L, w0L))) by smt. have -> : sk_R.`1 = sk_L.`1 by smt.
have -> : hash (sk_L.`1, x0L) = proj (pk_L.`1, x0L, w0L) by smt. smt. 
have <- : sk_L.`2 = sk_R.`2 by smt. smt.
split; first smt. 
have -> : sk_L = sk_R by smt. have -> : log_L = log_R by smt.  
have -> : cstar_L = cstar_R. 
have -> : cstar_L = Some c_L by smt. have -> : cstar_R = Some c_R by smt. 
have -> : c_L =  (x0L, e_L, proj_ (pk_L.`2, x0L, e_L, w0L)) by smt. 
have -> : c_R = (x0L, estar_R, hash_ (sk_R.`2, x0L, estar_R)) by smt. 
have -> : estar_R = e_L. have -> :  estar_R =  toY (toint (if bL then result_R.`2 else result_R.`1) + toint (hash (sk_R.`1, x0L))) by smt. 
have -> : e_L = toY (toint (if bL then result_L.`2 else result_L.`1) + toint (proj (pk_L.`1, x0L, w0L))) by smt. have -> : sk_R.`1 = sk_L.`1 by smt. have : result_R = result_L by smt. 
have -> : hash(sk_L.`1, x0L) = proj (pk_L.`1, x0L, w0L) by smt. smt.   
have -> : sk_R.`2 = sk_L.`2 by smt. smt. trivial. 
move => ? ? ? ? ? ? ? ?. have -> : result_R0 = result_L0 by smt. trivial. 
qed.

local lemma CCA_Game1_main_pr &m :
    Pr[CCA(Genscheme,A).main() @ &m : res] = Pr[Game1(A).main() @ &m : res]. 
by byequiv (CCA_Game1_main). qed.

(*** Change the simulator: sample x from xs `\` ls instead of from ls ***)
local module Game2(A:CCAadv) = {
  var log   : ciphertext list
  var cstar : ciphertext option
  var sk    : skey

  module O = {
    proc decrypt(c:ciphertext) : plaintext option = {
      var m : plaintext option;
      var y_', y;
      if (size log < qD && (Some c <> cstar)) {
        log <- c :: log;
        y_' <- HPS_Ext.priveval(sk.`2, c.`1, c.`2); 
        if (y_' = c.`3) {
          y <- HPS.priveval(sk.`1, c.`1);
          m <- Some (toY (toint c.`2 - toint y));
        } else m <- None;
      }
      else m <- None;
      return m;
    }
  }

  module A = A(O)

  proc main() : bool = {
    var xstar, pk, m0, m1, b, b', ystar, y_', estar, c;
     log     <- [];
     cstar   <- None;
     xstar   <- Sampling.fromXnotL();
    (pk, sk) <- Genscheme.keygen();
    (m0, m1) <- A.choose(pk);
       b     <$ {0,1};
     ystar   <- HPS.priveval(sk.`1, xstar);
     estar   <- toY (toint (b?m1:m0) + toint ystar);
       y_'   <- HPS_Ext.priveval(sk.`2, xstar, estar);
       c     <- (xstar, estar, y_');
     cstar   <- Some c;
       b'    <- A.guess(c);
    return (b = b');
  }
}.

(*** Proofs that the procedures of Game2 terminate ***)
local lemma Game2_O_ll : islossless Game2(A).O.decrypt. 
proof.
proc; inline*.
if => //; auto.  
qed.

local lemma Game2_main_ll : islossless Game2(A).main. 
proof. 
proc; inline*. 
call(_:true). 
  + by apply Ag_ll. 
proc; inline*. 
if => />. auto.  wp. skip. smt. 
auto. call(_:true). 
 + by apply Ac_ll. 
proc; inline*. 
if => //. auto. wp; skip; smt. 
auto; progress. smt. smt(dK_weight). smt(dK2_weight). smt(@DBool). 
qed. 

(*** Reduction from a CCA adversary to a SMP adversary ***)
local module SMPadv(A:CCAadv) = {
  var log   : ciphertext list
  var cstar : ciphertext option
  var sk    : skey

  module O = {
    proc decrypt(c:ciphertext) : plaintext option = {
      var m : plaintext option;
      var y_', y;
      if (size log < qD && (Some c <> cstar)) {
        log <- c :: log;
        y_' <- HPS_Ext.priveval(sk.`2, c.`1, c.`2); 
        if (y_' = c.`3) {
          y <- HPS.priveval(sk.`1, c.`1);
          m <- Some (toY (toint c.`2 - toint y));
        } else m <- None;
      }
      else m <- None;
      return m;
    }
  }


  module A = A(O)

  proc guess(x) : bool = {
    var m0, m1, b, b', ystar, y_', estar, c, pk;
     log     <- [];
     cstar   <- None;
    (pk, sk) <- Genscheme.keygen();
    (m0, m1) <- A.choose(pk);
       b     <$ {0,1};
     ystar   <- HPS.priveval(sk.`1, x);
     estar   <- toY (toint (b?m1:m0) + toint ystar);
       y_'   <- HPS_Ext.priveval(sk.`2, x, estar);
       c     <- (x, estar, y_');
     cstar   <- Some c;
       b'    <- A.guess(c);
    return (b = b');
  }
}.

(*** Proofs that the advantage in distinguishing between Game1 and Game2
   is equivalent to the SMP distinguishing advantage ***)
local equiv Game1_SMP1 : Game1(A).main ~ SMP1(SMPadv(A)).main : ={glob A} ==> ={res}. 
proof. 
proc. inline*. swap{2} [5 .. 6] -4. 
wp. swap{1} [16 .. 18] -13. 
call (_: Game1.sk{1} = SMPadv.sk{2} /\ Game1.cstar{1} = SMPadv.cstar{2} /\ Game1.log{1} = SMPadv.log{2}). 
proc;inline*;auto. 
sp. 
wp;rnd. 
call (_: Game1.sk{1} = SMPadv.sk{2} /\ Game1.cstar{1} = SMPadv.cstar{2} /\ Game1.log{1} = SMPadv.log{2}); first proc;inline*;auto. 
+ by auto. 
qed. 

local lemma Game1_SMP1_pr &m : Pr[Game1(A).main() @ &m : res] = Pr[SMP1(SMPadv(A)).main() @ &m : res] by byequiv Game1_SMP1. 

local equiv Game2_SMP0 : Game2(A).main ~ SMP0(SMPadv(A)).main : ={glob A} ==> ={res}. 
proof. 
proc. inline*. swap{2} [4 .. 5] -3. 
wp.  
call (_: Game2.sk{1} = SMPadv.sk{2} /\ Game2.cstar{1} = SMPadv.cstar{2} /\ Game2.log{1} = SMPadv.log{2}). 
proc;inline*;auto. 
sp. 
wp;rnd. 
call (_: Game2.sk{1} = SMPadv.sk{2} /\ Game2.cstar{1} = SMPadv.cstar{2} /\ Game2.log{1} = SMPadv.log{2}); first proc;inline*;auto. 
+ by auto. 
qed. 

local lemma Game2_SMP0_pr &m : Pr[Game2(A).main() @ &m : res] = Pr[SMP0(SMPadv(A)).main() @ &m : res] by byequiv (Game2_SMP0).  

(*** Modify the simulator: define a bad event, where bad is set to true if for any ciphertext 
     (x, e, y_), x is in xs `\` ls but yet hash_(x,e) = y_. ***)
local module Game3(A:CCAadv) = {
  var log   : ciphertext list
  var cstar : ciphertext option
  var sk    : skey
  var bad   : bool

  module O = {
    proc decrypt(c:ciphertext) : plaintext option = {
      var m : plaintext option;
      var y_', y;
      if (size log < qD && (Some c <> cstar)) {
        log <- c :: log;
        y_' <- HPS_Ext.priveval(sk.`2, c.`1, c.`2); 
        if (y_' = c.`3) {
          y <- HPS.priveval(sk.`1, c.`1);
          m <- Some (toY (toint c.`2 - toint y));
          if (!(c.`1 \in ls) /\ c.`3 = hash_(sk.`2, c.`1, c.`2)) {bad <- true;}
        } else m <- None;
      } 
      else m <- None;
      return m;
    }
  }

  module A = A(O)

  proc main() : bool = {
    var xstar, pk, m0, m1, b, b', ystar, y_', estar, c;
      log    <- [];
      cstar  <- None;
      bad    <- false;
      xstar  <- Sampling.fromXnotL();
    (pk, sk) <- Genscheme.keygen();
    (m0, m1) <- A.choose(pk);
       b     <$ {0,1};
     ystar   <- HPS.priveval(sk.`1, xstar);
     estar   <- toY (toint (b?m1:m0) + toint ystar);
       y_'   <- HPS_Ext.priveval(sk.`2, xstar, estar);
       c     <- (xstar, estar, y_');
     cstar   <- Some c;
       b'    <- A.guess(c);
    return (b = b');
  }
}.

(*** Proofs that the procedures of Game3 terminate ***)
local lemma Game3_O_ll : islossless Game3(A).O.decrypt.
proof.
proc; inline*. 
if => //; auto. 
qed.

local lemma Game3_main_ll : islossless Game3(A).main. 
proof.
proc; inline*.  
call(_:true). 
  + by apply Ag_ll. 
proc; inline*.
if => />. auto.  wp. skip. smt. 
auto. call(_:true). 
 + by apply Ac_ll. 
proc; inline*.
if => //. auto. wp; skip; smt. 
auto; progress. smt. smt(dK_weight). smt(dK2_weight). smt(@DBool).
qed. 

(*** Proof that if the bad event is not set to true, the decryption oracles of 
     Game2 and Game3 are equivalent ***)
local equiv Game2_ExpG2_decrypt_failure : Game2(A).O.decrypt ~ Game3(A).O.decrypt :
  !Game3.bad{2} /\ Game2.log{1} = Game3.log{2} /\ Game2.cstar{1} = Game3.cstar{2} /\ Game2.sk{1} = Game3.sk{2} /\ Some c{1} = Some c{2} ==>
  !Game3.bad{2} => Game2.log{1} = Game3.log{2} /\ Game2.cstar{1} = Game3.cstar{2} /\ Game2.sk{1} = Game3.sk{2} /\  ={res}.
proof. 
proc;inline*;auto. 
qed. 

(*** The following three lemmas are quite trivial, but yet necessary for some of the 
     tactics in some of the proofs below to pass ***)
local lemma Game3_bad : phoare[Game3(A).O.decrypt : Game3.bad ==> Game3.bad] = 1%r. 
proof.
proc;inline*;auto.
qed.  

local lemma xnotinL_bad (c:ciphertext) : phoare[Game3(A).O.decrypt : !(c.`1 \in ls) ==> !(c.`1 \in ls)] = 1%r.  
proc;inline*;auto. 
qed. 

local lemma hash_temp (c:ciphertext) : phoare[Game3(A).O.decrypt : c.`3 = hash_ (Game3.sk.`2,c.`1, c.`2) ==> c.`3 = hash_ (Game3.sk.`2, c.`1, c.`2)] = 1%r. 
proof.
by proc;inline*;auto. 
qed.

(*** Proof that the main procedures of Game2 and Game3 are equivalent if the 
     bad event is not set to true ***)
local equiv Game2_Game3_main_bad : Game2(A).main ~ Game3(A).main :
   ={glob A} ==> !Game3.bad{2} => ={res}.
proof. 
proc; inline*. 
call(_: Game2.log{1} = Game3.log{2} /\ Game2.cstar{1} = Game3.cstar{2} /\ Game2.sk{1} = Game3.sk{2}).  
proc;inline*;auto. 
wp; rnd. 
call(_: Game2.log{1} = Game3.log{2} /\ Game2.cstar{1} = Game3.cstar{2} /\ Game2.sk{1} = Game3.sk{2}).
proc;inline*;auto. 
wp. rnd. wp. rnd. wp.  rnd. wp. skip. progress. 
qed.

(*** Proof that the difference difference between the adversary winning Game2 and 
    the adversary winning Game3 is less than or equal to the bad event being set to true ***)
local lemma Game2_Game3_main_bad_pr &m : 
    Pr[Game2(A).main() @ &m : res] <= Pr[Game3(A).main() @ &m : res] + 
      Pr[Game3(A).main() @ &m : Game3.bad]. 
proof. 
byequiv (Game2_Game3_main_bad) => //;smt.
qed. 

local lemma Game2_Game3_main_bad_pr2 &m :
    Pr[Game2(A).main() @ &m : res] - Pr[Game3(A).main() @ &m : res] <=
      Pr[Game3(A).main() @ &m : Game3.bad] by smt(Game2_Game3_main_bad_pr).

(*** Proofs that the probability of the bad event being set to true is bounded by 
     the probability that the adversary has been able to guess a hash value 
     for some x not in ls ***)
local equiv bad_bound : Game3(A).main ~ Game3(A).main : 
  ={glob A} ==> exists c, c \in Game3.log{2} => (!c.`1 \in ls /\ c.`3 = hash_(Game3.sk{2}.`2, c.`1, c.`2) => Game3.bad{1}). 
proof. 
proc. inline*. 
 call (_: Game3.bad{1} = Game3.bad{2} /\ Game3.sk{1} = Game3.sk{2} /\ Game3.cstar{1} = Game3.cstar{2} /\ Game3.log{1} = Game3.log{2} /\ exists c, c \in Game3.log{2} => (!c.`1 \in ls /\ c.`3 = hash_(Game3.sk{2}.`2, c.`1, c.`2) => Game3.bad{1})). 
proc;inline*;auto. progress. smt. smt. smt. 
wp; rnd. 
call (_: Game3.bad{1} = Game3.bad{2} /\ Game3.sk{1} = Game3.sk{2} /\ Game3.cstar{1} = Game3.cstar{2} /\ Game3.log{1} = Game3.log{2} /\ exists c, c \in Game3.log{2} => (!c.`1 \in ls /\ c.`3 = hash_(Game3.sk{2}.`2, c.`1, c.`2) => Game3.bad{1})). 
proc;inline*;auto. progress. smt. smt. smt. 
wp. rnd. wp. rnd. wp. rnd. wp. skip.
move => ?????.  split; first exact/H0. 
move => ???. split; first exact/H2. 
move => ???. split; first exact/H4. 
move => ???. split; first smt. 
move => ????????????. split; first exact/H8. 
move => ???????. split. split. smt(). split; first smt. smt(). 
move => ??????????. smt(). 
qed. 

local lemma bad_bound_pr &m : Pr[Game3(A).main() @ &m : Game3.bad{m}] <=
  Pr[Game3(A).main() @ &m : exists c, c \in Game3.log => !c.`1 \in ls /\ c.`3 = hash_(Game3.sk.`2, c.`1, c.`2) => Game3.bad{m}]. 
byequiv (bad_bound). trivial. 
move => ????. smt. 
qed. 

local lemma bad_bound_pr2 &m : Pr[Game3(A).main() @ &m : exists c, c \in Game3.log => !c.`1 \in ls /\ c.`3 = hash_(Game3.sk.`2, c.`1, c.`2) => Game3.bad] <=
  Pr[Game3(A).main() @ &m : exists c, c \in Game3.log => !c.`1 \in ls /\ c.`3 = hash_(Game3.sk.`2, c.`1, c.`2)].
proof. 
byequiv (bad_bound). trivial.  
smt. 
qed.

local lemma bad_bound_pr3 &m : Pr[Game3(A).main() @ &m : Game3.bad] <=
  Pr[Game3(A).main() @ &m : exists c, c \in Game3.log => !c.`1 \in ls /\ c.`3 = hash_(Game3.sk.`2, c.`1, c.`2)]. 
proof. 
have : Pr[Game3(A).main() @ &m : Game3.bad] <= Pr[Game3(A).main() @ &m : exists c, c \in Game3.log => !c.`1 \in ls /\ c.`3 = hash_(Game3.sk.`2, c.`1, c.`2) => Game3.bad] by smt. move => H0. 
have : Pr[Game3(A).main() @ &m : exists c, c \in Game3.log => !c.`1 \in ls /\ c.`3 = hash_(Game3.sk.`2, c.`1, c.`2) => Game3.bad] <=
  Pr[Game3(A).main() @ &m : exists c, c \in Game3.log => !c.`1 \in ls /\ c.`3 = hash_(Game3.sk.`2, c.`1, c.`2)]. by apply (bad_bound_pr2 &m). 
move => ?.  
smt. 
qed. 

(*** Substituting the bad event by the event that the adversary has guessed a hash value
    for x not in ls ***)
local lemma Game2_Game3_conc_bad &m : 
  Pr[Game2(A).main() @ &m : res] - Pr[Game3(A).main() @ &m : res] <=
  Pr[Game3(A).main() @ &m :
       exists (c : ciphertext),
         c \in Game3.log =>
         ! (c.`1 \in ls) /\ c.`3 = hash_ (Game3.sk.`2, c.`1, c.`2)].
proof.
smt. 
qed.  

(*** Some lemmas proving that the adversary winning and the adversary not winning are 
    complementary events both in Game2 and Game3 ***)
local lemma Game2_comp1 &m : Pr[Game2(A).main() @ &m : res \/ !res] = 1%r.   
byphoare => //.  
proc;inline*. 
call(_:true); auto. apply Ag_ll. proc;inline*;auto. 
call(_:true). apply Ac_ll. proc;inline*;auto. 
auto. progress.  smt. smt. smt. smt. smt all. 
qed. 

local lemma Game2_comp2 &m : Pr[Game2(A).main() @ &m : res] + Pr[Game2(A).main() @ &m : !res] = 1%r.  
have : Pr[Game2(A).main() @ &m : res \/ !res] = 1%r by smt(Game2_comp1).  
rewrite Pr[mu_or]. 
have -> : Pr[Game2(A).main() @ &m : res /\ !res] = 0%r. 
byphoare =>//. 
proc;inline*. 
+ hoare. 
call(_:true). proc;inline*;auto.  
auto. 
call(_:true). proc;inline*;auto. 
auto. smt. smt.    
qed. 

local lemma Game2_comp3 &m :  Pr[Game2(A).main() @ &m : !res] = 1%r -  Pr[Game2(A).main() @ &m : res] by smt. 

local lemma Game3_comp1 &m : Pr[Game3(A).main() @ &m : res \/ !res] = 1%r.   
byphoare => //.  
proc;inline*. 
call(_:true); auto. apply Ag_ll. proc;inline*;auto. 
call(_:true). apply Ac_ll. proc;inline*;auto. 
auto. progress.  smt. smt. smt. smt. smt all. 
qed. 

local lemma Game3_comp2 &m : Pr[Game3(A).main() @ &m : res] + Pr[Game3(A).main() @ &m : !res] = 1%r.  
have : Pr[Game3(A).main() @ &m : res \/ !res] = 1%r by smt(Game3_comp1).  
rewrite Pr[mu_or]. 
have -> : Pr[Game3(A).main() @ &m : res /\ !res] = 0%r. 
byphoare =>//. 
proc;inline*. 
+ hoare. 
call(_:true). proc;inline*;auto.  
auto. 
call(_:true). proc;inline*;auto. 
auto. smt all. 
smt.   
qed. 

local lemma Game3_comp3 &m :  Pr[Game3(A).main() @ &m : !res] = 1%r -  Pr[Game3(A).main() @ &m : res] by smt. 

(*** Proofs that the absolute difference between the adversary winning Game2 and Game3 is bounded by the bad event being set to true ***)
local lemma Game2_Game3_uni2_abs &m : `|Pr[Game2(A).main() @ &m : res] - Pr[Game3(A).main() @ &m : res]| <= Pr[Game3(A).main() @ &m : Game3.bad].
proof. 
case: (Pr[Game2(A).main() @ &m : res] <= Pr[Game3(A).main() @ &m : res]) => Hle.   
have ->: `|Pr[Game2(A).main() @ &m : res] - Pr[Game3(A).main() @ &m : res]| = Pr[Game3(A).main() @ &m : res] - Pr[Game2(A).main() @ &m : res] by smt().  
have : Pr[Game2(A).main() @ &m : !res] <= Pr[Game3(A).main() @ &m : !res \/ Game3.bad].
byequiv.  proc;inline*. 
call(_: Game2.log{1} = Game3.log{2} /\ Game2.sk{1} = Game3.sk{2} /\ Game2.cstar{1} = Game3.cstar{2}). 
proc;inline*;auto. 
auto. call(_: Game2.log{1} = Game3.log{2} /\ Game2.sk{1} = Game3.sk{2} /\ Game2.cstar{1} = Game3.cstar{2}). 
proc;inline*;auto. 
auto. progress. smt(). trivial. smt().
rewrite Pr[mu_or] (Game2_comp3 &m) (Game3_comp3 &m). smt(mu_bounded). 
have -> : `|Pr[Game2(A).main() @ &m : res] - Pr[Game3(A).main() @ &m : res]| = Pr[Game2(A).main() @ &m : res] - Pr[Game3(A).main() @ &m : res] by smt(). 
apply (Game2_Game3_main_bad_pr2 &m). 
qed. 

local lemma bad_event_abs &m : Pr[Game3(A).main() @ &m : res] = `|Pr[Game3(A).main() @ &m : res]| by smt(mu_bounded). 

local lemma Game2_Game3_uni2_abs2 &m : `|Pr[Game2(A).main() @ &m : res] - Pr[Game3(A).main() @ &m : res]| <= `|Pr[Game3(A).main() @ &m : Game3.bad]| by smt(Game2_Game3_uni2_abs bad_event_abs). 

local lemma Game2_Game3_uni2_abs_finito &m : `|Pr[Game2(A).main() @ &m : res] - Pr[Game3(A).main() @ &m : res]| <= `|Pr[Game3(A).main() @ &m :
       exists (c : ciphertext),
         c \in Game3.log =>
         ! (c.`1 \in ls) /\ c.`3 = hash_ (Game3.sk.`2, c.`1, c.`2)]|. 
proof. 
smt(bad_bound_pr3 Game2_Game3_uni2_abs bad_event_abs). 
qed. 

(*** END OF EXP2G0 ~ EXP2G1 AND THE FAILURE EVENT ***)

(*** Modify the simulator: instead of computing y = hash(k,x) we sample y at random ***)
local module Game4(A:CCAadv) = {
  var log   : ciphertext list
  var cstar : ciphertext option
  var sk    : skey
  var bad   : bool

  module O = {
    proc decrypt(c:ciphertext) : plaintext option = {
      var m : plaintext option;
      var y_', y;
      if (size log < qD && (Some c <> cstar)) {
        log <- c :: log;
        y_' <- HPS_Ext.priveval(sk.`2, c.`1, c.`2); 
        if (y_' = c.`3) {
          y <- HPS.priveval(sk.`1, c.`1);
          m <- Some (toY (toint c.`2 - toint y));
          if (!(c.`1 \in ls) /\ c.`3 = hash_(sk.`2, c.`1, c.`2)) {bad <- true;}
        } else m <- None;
      } 
      else m <- None;
      return m;
    }
  }

  module A = A(O)

  proc main() : bool = {
    var xstar, pk, m0, m1, b, b', ystar, y_', estar, c;
      log    <- [];
     cstar   <- None;
      bad    <- false;
     xstar   <- Sampling.fromXnotL();
    (pk, sk) <- Genscheme.keygen();
    (m0, m1) <- A.choose(pk);
       b     <$ {0,1};
     ystar   <- Sampling.fromY();
     estar   <- toY (toint (b?m1:m0) + toint ystar);
       y_'   <- HPS_Ext.priveval(sk.`2, xstar, estar);
       c     <- (xstar, estar, y_');
     cstar   <- Some c;
       b'    <- A.guess(c);
    return (b = b');
  }
}.

(*** Proofs that the procedures of Game4 terminate ***)
local lemma Game4_O_ll : islossless Game4(A).O.decrypt.
proof.
proc; inline*. 
if => //; auto. 
qed.

local lemma Game4_main_ll : islossless Game4(A).main. 
proof.
proc; inline*.  
call(_:true). 
  + by apply Ag_ll. 
proc; inline*. 
if => />. auto.  wp. skip. smt. 
auto. call(_:true). 
 + by apply Ac_ll. 
proc; inline*. 
if => //. auto. wp; skip; smt. 
auto; progress. smt. smt(dK_weight). smt(dK2_weight). smt(@DBool). smt(ys_ful). 
qed. 

(*** Reduction from a CCA adversary to a smoothness adversary ***)
local module SmoothAdv(A:CCAadv) = {
  var log   : ciphertext list
  var cstar : ciphertext option
  var bad   : bool
  var sk    : skey
  var k     : K
  var k_    : K_

   module O = {
    proc decrypt(c:ciphertext) : plaintext option = {
      var m : plaintext option;
      var y_', y;
      if (size log < qD && (Some c <> cstar)) {
        log <- c :: log;
        y_' <- HPS_Ext.priveval(k_, c.`1, c.`2); 
        if (y_' = c.`3) {
          y <- HPS.priveval(k, c.`1);
          m <- Some (toY (toint c.`2 - toint y));
          if (!(c.`1 \in ls) /\ c.`3 = hash_(k_, c.`1, c.`2)) {bad <- true;}
        } else m <- None;
      } 
      else m <- None;
      return m;
    }
  } 

  module A = A(O)
   

  proc guess(x:X, s:S, y:Y) : bool = {
    var m0, m1, b, b', s_;
      log   <- [];
     cstar  <- None;
      bad   <- false;
       k_   <- HPS_Ext.kg();
       s_   <- HPS_Ext.seval(k_);
       sk   <- (k, k_);
    (m0,m1) <- A.choose(s,s_);
       b    <$ {0,1};
     cstar  <- Some (x, toY (toint (b?m1:m0) + toint y), hash_(k_, x, toY (toint (b?m1:m0) + toint y)));
       b'   <- A.guess(x, toY (toint (b?m1:m0) + toint y), hash_(k_, x, toY (toint (b?m1:m0) + toint y)));
    return (b = b');
  }
}. 

local module Smooth1(A:SmoothAdversary) = {
  proc main() : bool = {
    var b, x;
    x <- Sampling.fromXnotL();
    SmoothAdv.k <- HPS.kg();
    b <- A.guess(x, alpha SmoothAdv.k, hash(SmoothAdv.k,x));
    return b; 
  }
}.

local module Smooth0(A:SmoothAdversary) = {
  proc main() : bool = {
    var b, x, y;
    x <- Sampling.fromXnotL();
    SmoothAdv.k <- HPS.kg(); 
    y <- Sampling.fromY();
    b <- A.guess(x, alpha SmoothAdv.k, y);
    return b;
  }
}.

(*** Proof that the adversary's advantage in distinguish between Game3 and Game4 is 
    equivalent to the smoothness advantage, i.e. the advantage in distinguishing between
    (x, s, hash(k,x)) and (x, s, random y) for x not in ls ***)
local equiv Game3_Smooth1 : Game3(A).main ~ Smooth1(SmoothAdv(A)).main : ={glob A} ==> ={res}.   
proc. 
inline*.  wp.   
call (_: Game3.log{1} = SmoothAdv.log{2} /\ Game3.cstar{1} = SmoothAdv.cstar{2} /\ Game3.sk{1} = (SmoothAdv.k{2}, SmoothAdv.k_{2})).  proc;inline*;auto.  
swap {2} [8 .. 10] -7. sp. 
swap{2} 7 8.    
wp;rnd. 
call(_: Game3.log{1} = SmoothAdv.log{2} /\ Game3.cstar{1} = SmoothAdv.cstar{2} /\ Game3.sk{1} = (SmoothAdv.k{2}, SmoothAdv.k_{2}));  first proc; if => //; sp; inline*; wp; skip; progress.
wp.  rnd. wp. rnd. wp. rnd. skip.
move => ?????. split; first exact H0. 
move => ?. split; first trivial. move => ???. 
split; first exact H3. move => ?. split; first done. move => ???. 
split; first smt().  
move => ?. split; first smt(). move => ??. split. smt .
move => ????????????. split;first exact H11. move => ??????. 
split. split. smt(). 
smt().  
move => ????????. have -> : result_L0 = result_R0 by smt(). 
trivial. 
qed. 

local equiv Game4_Smooth0 : Game4(A).main ~ Smooth0(SmoothAdv(A)).main : ={glob A} ==> ={res}. 
proof. 
proc.
inline*. wp. 
call(_: Game4.log{1} = SmoothAdv.log{2} /\ Game4.sk{1} = (SmoothAdv.k{2}, SmoothAdv.k_{2}) /\ Game4.cstar{1} = SmoothAdv.cstar{2}); first proc; if => //=; sp; inline*; wp; skip; progress.  
swap{2} [10 .. 12] -9. sp. swap{2} [5 ..6] 2. swap{2} [7 .. 9] 8. 
wp; do 2! rnd. 
call(_: Game4.log{1} = SmoothAdv.log{2} /\ Game4.sk{1} = (SmoothAdv.k{2}, SmoothAdv.k_{2}) /\ Game4.cstar{1} = SmoothAdv.cstar{2}); first proc; if => //=; sp; inline*; wp; skip; progress.
auto.
qed. 

local lemma Game3_Smooth1_pr &m : Pr[Game3(A).main() @ &m : res] = Pr[Smooth1(SmoothAdv(A)).main() @ &m : res] by byequiv (Game3_Smooth1). 

local lemma Game4_Smooth0_pr &m : Pr[Game4(A).main() @ &m : res] = Pr[Smooth0(SmoothAdv(A)).main() @ &m : res] by byequiv (Game4_Smooth0). 

(*** END OF THE SMOOTHNESS PART ***)

(*** Change Game4 to make the adversary's output completely independent of the hidden bit b ***)
local module Game4indep(A:CCAadv) = {
  var log   : ciphertext list
  var cstar : ciphertext option
  var sk    : skey
  var bad   : bool

  module O = {
    proc decrypt(c:ciphertext) : plaintext option = {
      var m : plaintext option;
      var y_', y;
      if (size log < qD && (Some c <> cstar)) {
        log <- c :: log;
        y_' <- HPS_Ext.priveval(sk.`2, c.`1, c.`2); 
        if (y_' = c.`3) {
          y <- HPS.priveval(sk.`1, c.`1);
          m <- Some (toY (toint c.`2 - toint y));
          if (!(c.`1 \in ls) /\ c.`3 = hash_(sk.`2, c.`1, c.`2)) {bad <- true;}
        } else m <- None;
      } 
      else m <- None;
      return m;
    }
  }

  module A = A(O)

  proc main() : bool = {
    var xstar, pk, m0, m1, b, b', ystar, y_', estar, c;
      log    <- [];
     cstar   <- None;
      bad    <- false;
     xstar   <- Sampling.fromXnotL();
    (pk, sk) <- Genscheme.keygen();
    (m0, m1) <- A.choose(pk);
     ystar   <- Sampling.fromY();
     estar   <- toY (toint ystar);
       y_'   <- HPS_Ext.priveval(sk.`2, xstar, estar);
       c     <- (xstar, estar, y_');
     cstar   <- Some c;
       b'    <- A.guess(c);
       b     <$ {0,1};
    return (b = b');
  }
}.

(*** Proof that Game3 and Game3indep are equivalent ***)
local equiv Game4_Game4indep : Game4(A).main ~ Game4indep(A).main : ={glob A} ==> ={res}. 
proof. 
proc. swap{2} 13 -6. 
call(_: Game4.log{1} = Game4indep.log{2} /\ Game4.sk{1} = Game4indep.sk{2} /\ Game4.cstar{1} = Game4indep.cstar{2} /\ Game4.bad{1} = Game4indep.bad{2}). 
proc;inline*;auto. 
wp. inline HPS_Ext.priveval. wp. 
inline Sampling.fromY. wp. 
rnd (fun y, toY (toint y + toint (if b then m1 else m0)){2}) (fun y, toY (toint y - toint (if b then m1 else m0)){2}). 
rnd. call(_: Game4.log{1} = Game4indep.log{2} /\ Game4.sk{1} = Game4indep.sk{2} /\ Game4.cstar{1} = Game4indep.cstar{2} /\ Game4.bad{1} = Game4indep.bad{2}).
proc;inline*;auto. 
inline*. wp. rnd. wp. rnd. wp. rnd. wp. skip.
move => &1 &2 H0 xR xRsupp. split; first exact/xRsupp. move => _. 
split; first trivial. move => xReq. split; first smt. move => H1. split; first smt. 
move => H2 k0L k0Lsupp. split; first exact/k0Lsupp. move => _. 
split; first trivial. move => k0Leq k_. move => k_supp. split; first exact/k_supp. 
move => _. split; first trivial. move => k_eq sk_R sk_L. split; first smt.
move => H3. move => mL mR AL badL logL AR badR logR H4 m0_R m0_L.  
split; first smt. move => H5. split; first smt. move => H6. 
move => bL bLsupp. split; first exact/bLsupp. move => _.
split; first trivial. move => bLeq. split. smt(y1 y2). move => H7. 
split. smt(ys_ful). 
move => H8 ystarR ystarRsupp. split; first smt(ys_ful). move => H9. 
split. smt(y1 y2). move => H10 eR eL cR cstarR cL cstarL. split. smt.  
move => H11. 
move => rL rR aL b_L lL aR bR lR. move => H12. have -> : rL = rR by smt. 
trivial. 
qed. 

local lemma Game4indephalf &m : Pr[Game4indep(A).main() @ &m : res] = 1%r/2%r. 
proof. 
byphoare => //. 
proc. rnd. call(_:true). apply Ag_ll. 
proc;inline*;auto. 
inline*. 
wp. rnd. call(_:true). apply Ac_ll. proc;inline*;auto. 
wp. rnd. 
wp. rnd. wp. rnd. wp. skip. 
progress. have -> : (forall (result : bool), mu {0,1} (transpose (=) result) = inv 2%r) = true by smt(@Distr @DBool). smt(@Distr ys_ful). smt(dK2_weight). smt(dK_weight). smt. 
qed. 

local lemma Game4_Game4indep_pr &m : 
  Pr[Game4(A).main() @ &m : res] = Pr[Game4indep(A).main() @ &m : res]
by byequiv (Game4_Game4indep). 

(*** Using the fact that Game4 and Game4indep are equivalent to prove that
    the adversary's advantage in Game4 is 1/2 ***)
local lemma Game4_half &m : Pr[Game4(A).main() @ &m : res] = 1%r/2%r by
rewrite (Game4_Game4indep_pr &m) (Game4indephalf &m). 

(*** The finalt reduction ***)
local lemma secure &m : 
  `|Pr[CCA(Genscheme,A).main() @ &m : res] - 1%r/2%r| <=
  `|Pr[SMP1(SMPadv(A)).main() @ &m : res] - Pr[SMP0(SMPadv(A)).main() @ &m : res]| + 
  `|Pr[Smooth1(SmoothAdv(A)).main() @ &m : res] - Pr[Smooth0(SmoothAdv(A)).main() @ &m : res]|    
+ `|Pr[Game3(A).main() @ &m : exists c, c \in Game3.log => !c.`1 \in ls /\ c.`3 = hash_(Game3.sk.`2, c.`1, c.`2)]|.
proof. 
rewrite -(Game1_SMP1_pr &m) -(Game2_SMP0_pr &m) -(Game3_Smooth1_pr &m) -(Game4_Smooth0_pr &m). 
have H0 //= : `|Pr[Game2(A).main() @ &m : res] - Pr[Game3(A).main() @ &m : res]| <= `|Pr[Game3(A).main() @ &m :
     exists (c : ciphertext),
       c \in Game3.log =>
       ! (c.`1 \in ls) /\ c.`3 = hash_ (Game3.sk.`2, c.`1, c.`2)]| by smt(Game2_Game3_uni2_abs_finito). 
rewrite(Game4_half &m).  
rewrite (CCA_Game1_main_pr &m). smt().  
qed.  

print lemma secure. 

end section Security.
