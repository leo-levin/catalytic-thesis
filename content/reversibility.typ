#import "../preamble.typ": *

=== Reversibility

#definition[
  A _catalytic Turing machine_ $mM$ with work space $s$ and catalytic space $c$ is a deterministic Turing machine with a read-only input tape, a work tape of $s(n)$ bits initially blank, and a catalytic tape of $c(n)$ bits that initially holds an arbitrary string $tau in {0,1}^(c(n))$. Each halting state of $mM$ is labeled with an output bit. If $mM$ halts on input $x$ with initial catalytic tape $tau$, we write $mM^tau (x)$ for its output and $C_mM (x, tau)$ for the contents of the catalytic tape when it halts.
]

Throughout this section, $s >= log n$, $c <= 2^(O(s))$, and $mM$ halts on every input and every initial catalytic tape.

#definition[
  A _configuration_ of $mM$ on inputs of length $n$ is a pair $sigma = chl gamma, v chr$, where $gamma in {0,1}^c$ is the contents of the catalytic tape and $v$ records the control state, the contents of the work tape, and the positions of the input, work, and catalytic heads.
]

The $v$ part has $O(1) + s + O(log n) + O(log s) + O(log c) = O(s)$ bits, using $s >= log n$ and $c <= 2^(O(s))$. So a machine with $O(s)$ work space can store the $v$ part of a configuration on its work tape.

#definition[
  A configuration is _halting_ if its control state is a halting state, and its _output_ is the bit $mM$ outputs in that state. For $x in {0,1}^n$ and a non-halting configuration $sigma$, let $Gamma_x (sigma)$ be the configuration after one step of $mM$ on input $x$ from $sigma$. For halting $sigma$, $Gamma_x (sigma)$ is undefined.
]

#definition[
  For $tau in {0,1}^c$, the _start configuration_ $start(tau)$ has catalytic tape $tau$, the start state, a blank work tape, and all heads at position $0$. We encode $v$ so that $start(tau) = chl tau, 0 dots 0 chr$.
]

So whether $sigma$ is a start configuration depends only on its $v$ part, not on $gamma$.

#definition[
  Let $x in {0,1}^n$ and $tau in {0,1}^c$. Since $mM$ halts on input $x$ with initial catalytic tape $tau$, applying $Gamma_x$ repeatedly to $start(tau)$ eventually reaches a halting configuration, which we call $h_(x,tau)$.
]

So $mM^tau (x)$ is the output of $h_(x,tau)$, and $C_mM (x, tau)$ is the catalytic tape of $h_(x,tau)$.

#definition[
  The _configuration graph_ $gG_x$ of $mM$ on $x$ has a node for every configuration, including those not reachable from any start configuration, and an edge from $sigma$ to $Gamma_x (sigma)$ for every non-halting $sigma$.

  Two configurations are in the same _component_ of $gG_x$ if they are connected by a path in $gG_x$ with edge directions ignored. For $tau in {0,1}^c$, let $gG_(x,tau)$ be the component of $gG_x$ containing $start(tau)$.
]

#remark[
  Configurations do not depend on $x$, but $Gamma_x$, $gG_x$, $h_(x,tau)$, and $gG_(x,tau)$ do. When the input $x$ is clear, we write $Gamma$, $gG$, $h_tau$, and $gG_tau$.
]

#lemma[
  For every $tau in {0,1}^c$, $gG_tau$ is a tree (when directions are ignored), $h_tau$ is the only halting configuration in $gG_tau$, and applying $Gamma$ repeatedly to any configuration in $gG_tau$ eventually reaches $h_tau$. In particular, if $start(tau') in gG_tau$ then $gG_(tau') = gG_tau$ and $h_(tau') = h_tau$.
] <tree>

#proof[
  Treat $gG_tau$ as a multigraph with directions ignored, with $V$ nodes, $ell$ of them halting. Any edge incident to a vertex in $gG_tau$ lies in $gG_tau$, and each non-halting node has exactly one outgoing edge while halting nodes have none, so $gG_tau$ has $V - ell$ edges. Since $gG_tau$ is connected, $V - ell >= V - 1$, so $ell <= 1$. Running $mM$ from $start(tau)$ reaches $h_tau$, so $h_tau in gG_tau$, so $ell = 1$. Hence $gG_tau$ is connected with $V - 1$ edges, so it is a tree.

  Let $sigma in gG_tau$. The sequence $sigma, Gamma(sigma), Gamma(Gamma(sigma)), dots$ stays in $gG_tau$. If no term of this sequence were halting, then by finiteness some configuration would appear twice, giving a cycle. Since $gG_tau$ is a tree, we must have that for some $k$, $Gamma^k (sigma)$ is a halting configuration in $gG_tau$, so $Gamma^k (sigma) = h_tau$.

  If $start(tau') in gG_tau$, then $gG_(tau') = gG_tau$, and $h_(tau')$ is a halting configuration in $gG_(tau')$, so $h_(tau') = h_tau$.]

#definition[
  In $gG_tau$, call $h_tau$ the _root_. For $sigma != h_tau$, the _parent_ of $sigma$ is $Gamma(sigma)$. The _children_ of $sigma$ are the configurations $rho$ with $Gamma(rho) = sigma$. The _subtree_ of $sigma$ consists of the configurations from which applying $Gamma$ repeatedly reaches $sigma$, including $sigma$ itself.
]

#proposition[
  Every configuration has $O(1)$ children, there is a fixed ordering of the children of each configuration, and there are deterministic catalytic subroutines using $O(s)$ work space that, given a configuration $sigma = chl gamma, v chr$ with $gamma$ on the catalytic tape and $v$ on the work tape, do the following:
  - $sans("Parent")^gamma (v)$: for non-halting $sigma$, change the configuration to $Gamma(sigma)$.
  - $sans("Rank")^gamma (v)$: for non-halting $sigma$, return the position of $sigma$ in the ordering of the children of $Gamma(sigma)$, leaving $gamma$ unchanged.
  - $sans("NumChildren")^gamma (v)$: return the number of children of $sigma$, leaving $gamma$ unchanged.
  - $sans("Child")^gamma (v, i)$:  change the configuration to the $i$-th child of $sigma$.
] <local>
#proof[
  \
  #h(3em) _To do_
]

Using the ordering from @local, we speak of the _first_ and _last_ child of a configuration, and of the _next_ and _previous_ sibling of a non-halting configuration among the children of its parent.


#definition[
  A _position_ is a pair $(sigma, a)$, where $sigma$ is a configuration and $a in {down, up}$.
]
Informally, $(chl gamma, v chr, down)$ means the walk is about to explore the subtree of $chl gamma, v chr$, and $(chl gamma, v chr, up)$ means it has finished that subtree and is heading back toward the root.

The machines $mM_->$ and $mM_<-$ take a position $(chl gamma, v chr, a)$ with $gamma$ on the catalytic tape and $v, a$ on the work tape.

#pseudo(name: $mM^gamma_->(v, a)$)[
  + *If* $a = down$:
    + $d <- sans("NumChildren")^gamma (v)$
    + *If* $d = 0$: *return* $(v, up)$ #comment[no children]
    + *Else:*
      + $v <- sans("Child")^gamma (v, 1)$ #comment[$chl gamma, v chr <-$ first child of $chl gamma, v chr$]
      + *Return* $(v, down)$
  + *If* $a = up$:
    + *If* $v$ is halting: *return* $(v, down)$ #comment[at the root]
    + *Else:*
      + $k <- sans("Rank")^gamma (v)$
      + $v <- sans("Parent")^gamma (v)$ #comment[$chl gamma, v chr <- Gamma (chl gamma, v chr)$]
      + $d <- sans("NumChildren")^gamma (v)$
      + *If* $k = d$: *return* $(v, up)$ #comment[came from the last child]
      + *Else:*
        + $v <- sans("Child")^gamma (v, k + 1)$ #comment[$chl gamma, v chr <-$ next sibling]
    + *Return* $(v, down)$
]

#pseudo(name: $mM^gamma_<-(v, a)$)[
  + *If* $a = up$:
    + $d <- sans("NumChildren")^gamma (v)$
    + *If* $d = 0$: *return* $(v, down)$ #comment[no children]
    + *Else:*
      + $v <- sans("Child")^gamma (v, d)$ #comment[$chl gamma, v chr <-$ last child of $chl gamma, v chr$]
      + *Return* $(v, up)$
  + *If* $a = down$:
    + *If* $v$ is halting: *return* $(v, up)$ #comment[at the root]
    + *Else:*
      + $k <- sans("Rank")^gamma (v)$
      + $v <- sans("Parent")^gamma (v)$ #comment[$chl gamma, v chr <- Gamma (chl gamma, v chr)$]
      + *If* $k = 1$: *return* $(v, down)$ #comment[came from the first child]
      + *Else:*
        + $v <- sans("Child")^gamma (v, k - 1)$ #comment[$chl gamma, v chr <-$ previous sibling]
    + *Return* $(v, up)$
]

By @local, $k$ and $d$ take $O(1)$ bits, so $mM^gamma_->$ and $mM^gamma_<-$ use $O(s)$ work space: they store only $v$, $a$, $k$, $d$, and the space used by the subroutines of @local.

#definition[
  If $mM_->^gamma (v,a)$ returns $(v', a')$ and leaves $gamma'$ on the catalytic tape, let $Pi(chl gamma, v chr, a) = (chl gamma', v' chr, a')$. Define $Pi inv$ from $mM_<-$ in the same way.
]

#proposition[
  For every configuration $sigma$:
  - $Pi(sigma, down)$ is $(rho, down)$ if $sigma$ has a first child $rho$, and $(sigma, up)$ if $sigma$ has no children.
  - $Pi(sigma, up)$ is $(sigma, down)$ if $sigma$ is halting, $(rho, down)$ if $sigma$ has a next sibling $rho$, and $(Gamma(sigma), up)$ otherwise.
  - $Pi inv (sigma, up)$ is $(rho, up)$ if $sigma$ has a last child $rho$, and $(sigma, down)$ if $sigma$ has no children.
  - $Pi inv (sigma, down)$ is $(sigma, up)$ if $sigma$ is halting, $(Gamma(sigma), down)$ if $sigma$ is the first child of $Gamma(sigma)$, and $(rho, up)$ if $sigma$ has a previous sibling $rho$.
] <walk-rules>
#proof[
  Consider $Pi(sigma, up)$ with $sigma$ non-halting. By @local, $sans("Rank")$ sets $k$ so that $sigma$ is the $k$-th child of $Gamma(sigma)$, $sans("Parent")$ moves to $Gamma(sigma)$, and $sans("NumChildren")$ sets $d$ to the number of children of $Gamma(sigma)$. If $k = d$, then $sigma$ is the last child, and $mM^gamma_->$ returns $(Gamma(sigma), up)$. Otherwise, the next sibling of $sigma$ is the $(k+1)$-th child of $Gamma(sigma)$, and $mM^gamma_->$ moves there and returns $down$. The remaining cases are similar. In $mM^gamma_<-$, $k = 1$ means $sigma$ is the first child of $Gamma(sigma)$, and the $(k-1)$-th child is its previous sibling.
]

#lemma[
  For every position $p$, $Pi inv (Pi(p)) = p$ and $Pi(Pi inv (p)) = p$.
] <undo>
#proof[
  We first show $Pi inv (Pi(p)) = p$:
  - If $sigma$ has a first child $rho$, then $Pi(sigma, down) = (rho, down)$. Since $rho$ is not halting and is the first child of $Gamma(rho) = sigma$, we get $Pi inv (rho, down) = (sigma, down)$.
  - If $sigma$ has no children, then $Pi(sigma, down) = (sigma, up)$, and $Pi inv (sigma, up) = (sigma, down)$.
  - If $sigma$ is halting, then $Pi(sigma, up) = (sigma, down)$, and $Pi inv (sigma, down) = (sigma, up)$.
  - If $sigma$ has a next sibling $rho$, then $Pi(sigma, up) = (rho, down)$. Since $rho$ is not halting and its previous sibling is $sigma$, we get $Pi inv (rho, down) = (sigma, up)$.
  - Otherwise, $sigma$ is the last child of $Gamma(sigma)$, so $Pi(sigma, up) = (Gamma(sigma), up)$ and $Pi inv (Gamma(sigma), up) = (sigma, up)$.

  So $Pi$ is injective. There are finitely many positions $(chl v, gamma chr, a)$ , so $Pi$ is a bijection. Given $p$, write $p = Pi(q)$. Then $Pi(Pi inv (p)) = Pi(Pi inv (Pi(q))) = Pi(q) = p$.]

#lemma[
  Let $sigma in gG_tau$. Starting at $(sigma, down)$ and applying $Pi$ until first reaching $(sigma, up)$, the walk visits $(rho, down)$ and $(rho, up)$ exactly once for every $rho$ in the subtree of $sigma$, and visits no other positions.
] <subtree>
#proof[
  \
  #h(3em) _To do_
]

#definition[
  The _tour_ of $gG_tau$ is the list of positions visited by starting at $(h_tau, down)$ and applying $Pi$ until first reaching $(h_tau, up)$.
]

#proposition[
  The tour of $gG_tau$ contains every position $(sigma, down)$ and $(sigma, up)$ with $sigma in gG_tau$ exactly once, and ends at $(h_tau, up)$. So, starting from any such position and applying $Pi$ repeatedly moves along the rest of the tour and reaches $(h_tau, up)$, and every position passed on the way has its configuration in $gG_tau$.
] <tour>

#proof[
  \
  #h(3em) _To do_
]

#definition[
  Let $B_(mM, x) = {tau in {0,1}^c : C_mM (x, tau) != tau}$. Call $tau$ _first_ if, starting at $(start(tau), up)$ and applying $Pi$, the walk reaches $(h_tau, up)$ before any $(start(tau'), up)$ with $tau' != tau$. Let $F_(mM, x)$ be the set of first tapes.
]

#lemma[$2^c - abs(F_(mM, x)) <= abs(B_(mM,x))$.
] <first>
#proof[
  \
  #h(3em) _To do_
]
