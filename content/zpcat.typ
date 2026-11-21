#import "../preamble.typ": *

=== $bold(PP_CAT#CSPACE;(s, c, 1 - 2^(-k)) subs ZP_CAT#CSPACE;(O(s) + k, O(k c)))$
#definition[
  Let $delta: NN -> [0,1]$. A language $L$ is in $PP_CAT#CSPACE;(s, c, delta)$ if there is a deterministic catalytic machine $mM$ with $s(n)$ bits of work space and $c(n)$ bits of catalytic space, halting on every input and every initial catalytic tape, such that for every $x in {0,1}^n$:
  - $mM^tau (x) = L(x)$ for every $tau in {0,1}^(c(n))$, and
  - $abs({tau in {0,1}^(c(n)) : C_mM (x, tau) != tau}) <= delta(n) dot 2^(c(n))$.
]
\
#definition[
  A language $L$ is in $ZP_CAT#CSPACE;(s, c)$ if there is a deterministic catalytic machine $zZ$ with $s(n)$ bits of work space and $c(n)$ bits of catalytic space, halting on every input and every initial catalytic tape, such that for every $x in {0,1}^n$:
  - $C_zZ (x, tau) = tau$ for every $tau in {0,1}^(c(n))$,
  - $zZ^tau (x) in {L(x), bot}$ for every $tau in {0,1}^(c(n))$, and
  - $abs({tau in {0,1}^(c(n)) : zZ^tau (x) = bot}) <= 1/2 dot 2^(c(n))$.
]
\
We show $PP_CAT#CSPACE;(s, c, 1 - 2^(-k)) subs ZP_CAT#CSPACE;(O(s) + k, O(k c))$.

The $ZP_CAT$ machine $zZ$ generates candidate tapes for the $PP_CAT$ $mM$ from its own catalytic tape and runs a simulation of $mM$ on each generated catalytic tape. The simulation succeeds exactly when the candidate is a _first_ tape, one whose walk reaches a halt before passing any other start. At least a $2^(-k)$ fraction of tapes are first, so about $2^k$ candidates are needed. Fully independent candidates would cost about $2^k c$ catalytic bits. Pairwise independent candidates suffice (@hitting) and cost only $O(k c)$ catalytic bits.
\
#definition[  Random variables $gamma_1, dots, gamma_N in {0,1}^c$ are  _pairwise independent and uniform_ if for all $i !=j$ and all $y,y' in {0,1}^c$,
  $
    PP[gamma_i = y, gamma_j = y'] = 2^(-2c)
  $
]

#lemma[
  Let $F subs {0,1}^c$ non-empty, and let $(gamma_i)$ be $N$ pairwise independent and
  uniform strings. Then
  $ PP[gamma_i in.not F "for all" i] <= 2^c / (N abs(F)). $
] <hitting>

#proof[
  Let $X_i = 1$ if $gamma_i in F$ and $X_i = 0$ if $gamma_i in.not F$. Let $X = sum X_i$, so $X = 0$ if and only if $gamma_i in.not F$ for all $i$. Each $gamma_i$ is uniform, and $F$ is a fixed set, so
  $
    EE[X_i] = PP[gamma_i in F] = abs(F)/2^c.
  $

  By linearity of expectation,

  #numbered[
    $
      EE[X] = sum EE[X_i] = (N abs(F))/2^c.
    $
  ] <mean>

  Since $X = sum X_i$,
  $
    "Var"[X] = sum_(i=1)^N "Var"[X_i] + sum_(i != j) "Cov"(X_i, X_j)
  $

  Because the $gamma_i$'s are pairwise independent, the $X_i$'s are pairwise independent. So for any $i, j$ with $i eq.not j$, $"Cov"(X_i, X_j)=0$. Since each $X_i in {0,1}$, $"Var"[X_i] = EE[X_i]- EE[X_i]^2<= EE[X_i]$, so $"Var"[X_i] <= EE[X_i]$. Therefore,
  $
    "Var"[X] <= sum EE[X_i] = EE[X]
  $

  If $X = 0$ then $abs(X - EE[X]) = EE[X]$, and $EE[X] > 0$ since $F$ is nonempty. So by Chebyshev's inequality and @mean,
  $
    PP[gamma_i in.not F "for all" i] & = PP[X = 0] \
                                     & <= PP[abs(X - EE[X]) >= EE[X]] \
                                     & <= "Var"[X] / EE[X]^2 \
                                     & <= 1 / EE[X] = 2^c / (N abs(F)).
  $]

#lemma[
  Let $m >= 1$, and let $w_0, dots, w_(m-1), gamma_0$ be independent uniform strings in ${0,1}^c$. For each $i in {0,1}^m$, let
  $ W_i = xor.big_({u : i[u] = 1}) w_u quad "and" quad gamma_i = gamma_0 xor W_i. $
  Then the $2^m$ strings $gamma_i$ are pairwise independent and uniform.
] <sampler>
#proof[
  Fix $i, j in {0,1}^m$ with $i != j$. Note
  $
    gamma_i xor gamma_j = (gamma_0 xor W_i) xor (gamma_0 xor W_j) = W_i xor W_j = xor.big_({u : i[u] != j[u]}) w_u,
  $

  since $gamma_0$ cancels, and so does any $w_u$ with $i[u] = j[u] = 1$. Since $i != j$, there is some $d$ with $i[d] != j[d]$, so $w_d$ is part of the sum. Write
  $
    gamma_i xor gamma_j = w_d xor R,
  $
  where $R$ is the XOR of the other $w_u$ in the sum. Since $R$ depends only on blocks other than $w_d$, it is independent of $w_d$. So for any $z in {0,1}^c$,
  #numbered(
    $
      PP[gamma_i xor gamma_j = z] & = sum_(r in {0,1}^c) PP[R = r] dot PP[w_d = z xor r] \
                                  & = sum_(r in {0,1}^c) PP[R = r] dot 2^(-c) \
                                  & = 2^(-c).
    $,
  ) <diff>
  That is, $gamma_i xor gamma_j$ is uniform.

  Now fix $y, y' in {0,1}^c$. Since $gamma_j = gamma_i xor (gamma_i xor gamma_j)$,
  $
    PP[gamma_i = y, gamma_j = y'] = PP[gamma_i = y, gamma_i xor gamma_j = y xor y'].
  $
  Since $gamma_i = gamma_0 xor W_i$, we have $gamma_i = y$ exactly when $gamma_0 = y xor W_i$. Both $W_i$ and $gamma_i xor gamma_j$ depend only on the $w_u$, so they are independent of $gamma_0$. Splitting up over the value $v$ of $W_i$,

  $
    PP[gamma_i = y, gamma_j = y'] & = sum_(v in {0,1}^c) PP[W_i = v, gamma_i xor gamma_j = y xor y'] dot PP[gamma_0 = y xor v] \
    & = 2^(-c) dot sum_(v in {0,1}^c) PP[W_i = v, gamma_i xor gamma_j = y xor y'] \
    & = 2^(-c) dot PP[gamma_i xor gamma_j = y xor y'] \
    & = 2^(-2c),
  $
  where the last step is @diff. Since $i != j$ were arbitrary labels, this is the definition of pairwise independent and uniform for the $2^m$ strings $gamma_i$.]

#remark[The $m+1$ uniformly random strings $w_0, dots, w_(m-1), gamma_0$ give $2^m$ pairwise independent $gamma_i$'s, one for each subset of the $w_u$'s.]

#theorem[
  Let $s >= log n$, $c <= 2^O(s)$, and $1 <= k <= 2^O(s)$, where $c$ and $k$ are computable in space $O(s)$. Then
  $
    PP_CAT#CSPACE;(s, c, 1 - 2^(-k)) subs ZP_CAT#CSPACE;(O(s) + k, O(k c)).
  $
]
#proof[Let $L in PP_CAT#CSPACE;(s, c, 1 - 2^(-k))$ be decided by a machine $mM$, and fix $x in {0,1}^n$. Let $B = {tau in {0,1}^c : C_mM (x, tau) != tau}$ be the set of tapes $mM$ does not restore, so $abs(B) <= (1 - 2^(-k)) 2^c$. Let $Pi$ and $Pi inv$ be the forward and backward walks on positions of $mM$ on $x$.

  Call $tau$ a _first_ tape if, starting at $(start(tau), up)$ and applying $Pi$, the walk reaches $(h_tau, up)$ before any $(start(tau'), up)$ with $tau' != tau$, and let $F subs {0,1}^c$ be the set of first tapes. Each component $gG_tau$ contains exactly one first tape, and all but at most one of its tapes are in $B$ (@first). So
  $
    2^c - abs(F) <= abs(B) <= (1 - 2^(-k)) 2^c,
  $
  hence $abs(F) >= 2^(c-k)$. In particular, $F$ is nonempty.

  Define $zZ$ as follows. $zZ$ has $O(s) + k$ work space and $(k+2) c = O(k c)$ catalytic space, and splits its initial catalytic tape into $k + 2$ strings
  $ w_0, w_1, dots, w_(k), gamma in {0,1}^c. $

  These $w_0, w_1, dots, w_(k)$ are used in $zZ$ to compute $W_i$ as in
  @sampler. Let $gamma_0$ be the initial value of $gamma$, and $gamma_i = gamma_0 xor W_i$.
  #pseudo(name: $zZ(x)$)[
    + *For each* $i in {0,1}^(k+1)$:
      + #line-label(<line:set>) $gamma <- gamma xor W_i$ #comment[$gamma$ now holds $gamma_i$]
      + $p <- (start(gamma), up)$
      + *Repeat:*
        + $p <- Pi(p)$
      + *until* $p = (sigma, up)$ with $sigma$ halting or a start config #comment[Terminates by @tour]
      + *If* $sigma$ is halting:
        + $r <-$ output of $sigma$
      + *Else*
        + $r <- bot$
      + *Repeat:*
        + $p <- Pi inv (p)$
      + *until* $p = (sigma, up)$ with $sigma$ a start config #comment[$p = (start(gamma_i), up)$, so $gamma$ holds $gamma_i$]
      + #line-label(<line:restore>) $gamma <- gamma xor W_i$ #comment[$gamma$ holds $gamma_0$ again]
      + *If* $r != bot$:
        + *Output* $r$
    + *Output* $bot$
  ]

  The forward walk terminates by @tour, the backward walk terminates because it retraces the forward walk (@undo), and the loop runs $2^(k+1)$ times, so $zZ$ halts on every input and initial tape.

  Note that $zZ$ always restores the catalytic tape. Given catalytic tape $tau$, $zZ$ breaks $tau$ into $w_0, w_1, dots, w_(k), gamma in {0,1}^c$, where $gamma$ initially holds $gamma_0$. The $w_u$ are never written over, and at the start of each iteration $gamma$ holds $gamma_0$: @line:set[line] sets $gamma$ to $gamma_i$, the backward walk retraces the forward walk (@undo) and so ends at $(start(gamma_i), up)$ with $gamma$ holding $gamma_i$, and @line:restore[line] returns $gamma$ to $gamma_0$. Since $zZ$ only outputs after @line:restore[line], $C_zZ (x, tau) = tau$ for every initial tape $tau$.

  The forward walk along $Pi$ stops at a position $(sigma, up)$ with $sigma$ halting exactly when $gamma_i in F$, and then $sigma = h_(gamma_i)$ by @tour. So $r$, the output of $h_(gamma_i)$, is $mM^(gamma_i) (x)$, which is $L(x)$ since $mM$ is always correct. Hence every non-$bot$ output of $zZ$ agrees with $L(x)$.

  $zZ$ outputs $bot$ exactly when no $gamma_i$ is in $F$. If $tau$ is uniform, then $w_0, dots, w_(k), gamma_0$ are independent and uniform, so the $2^(k+1)$ strings $gamma_i$ are pairwise independent and uniform by @sampler (with $m = k + 1$). Since $F$ depends only on $mM$ and $x$, @hitting gives
  $
    PP_tau [zZ^tau (x) = bot] <= 2^c / (2^(k+1) abs(F)) <= 2^c / (2^(k+1) dot 2^(c-k)) = 1/2.
  $
  So $zZ$ outputs $bot$ on no more than half of initial tapes.

  Finally, the work tape holds the loop counter $i$ ($k+1$ bits), the block index and bit position used to compute $W_i$ ($O(log k + log c)$ bits), and $r$, the $v$ part and direction bit of $p$, and scratch space for $Pi$ and $Pi inv$ ($O(s)$ bits, by @local). Since $log c = O(s)$, this is $O(s) + k$, and the catalytic tape has $(k+2)c = O(k c)$ bits. Therefore $L in ZP_CAT#CSPACE;(O(s) + k, O(k c))$.]
