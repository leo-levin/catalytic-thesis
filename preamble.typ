#import "@preview/lovelace:0.3.0": *
#import "@preview/zebraw:0.6.1": *


#import "@preview/ctheorems:2.0.0": *
#import thm-themes.ams: *

// number 1, 2, 3, … instead of prefixing with the heading number
#let sketch = proof.with(supplement: "Proof sketch")
#let theorem = theorem.with(base: none)
#let lemma = lemma.with(base: none)
#let proposition = proposition.with(base: none)
#let definition = definition.with(base: none)
#let claim = claim.with(base: none)



// ── Page setup ───────────────────────────────
#let init(title: "", author: "Leo Frankel", body) = {
  show: thm-rules.with(qed-symbol: $square$)
  let short = (
    "Theorem": [Thm.],
    "Definition": [Defn.],
    "Lemma": [Lem.],
    "Proposition": [Prop.],
    "Corollary": [Cor.],
    "Remark": [Rmk.],
  )
  show ref: it => {
    let el = it.element
    if it.supplement == auto and el != none and el.func() == figure {
      let name = el.supplement.at("text", default: none)
      if name != none and name in short {
        return ref(it.target, supplement: short.at(name))
      }
    }
    it
  }
  set page(
    header: context { if counter(page).get().first() > 1 [#title #h(1fr) #counter(page).display("1/1", both: true)] },
  )
  show heading.where(level: 3): it => [#v(1em)#it#v(-1em)#line(length: 100%)]
  show heading.where(level: 2): it => [#v(1em)#it#v(-1em)#line(length: 100%)]

  show math.equation.where(block: true): set block(above: 0.8em, below: 0.6em)
  show math.equation.where(block: false): box
  set enum(spacing: 1em, indent: 5pt)
  set list(spacing: 0.88em, indent: 5pt)

  body
}

// ── Helpers ──────────────────────────────────
//

#let comment(body) = {
  h(1fr)
  text(fill: luma(110), size: 0.9em)[#body]
}
#let numbered(body) = math.equation(
  block: true,
  supplement: [Eq.],
  numbering: (..nums) => context {
    let ours = query(math.equation.where(block: true)).filter(e => e.has("supplement") and e.supplement == [Eq.])
    let n = nums.pos().first()
    let idx = ours.position(e => counter(math.equation).at(e.location()).first() == n)
    "(" + str(idx + 1) + ")"
  },
  body,
)
#let qed = {
  h(1fr)
  $square$
  linebreak()
}

#let pseudo(name: none, content) = block(
  fill: luma(240),
  inset: (x: 2em, y: .5em),
  radius: 4pt,
  width: 100%,
  breakable: true,
  {
    v(-.5em)
    pseudocode-list(hooks: .5em, {
      if name != none [#h(-1em)*#name*]
      content
    })
    v(-.5em)
  },
)
// ── General math ─────────────────────────────
#let phi = $phi.alt$
#let ov(x) = $overline(#x)$
#let gn(x) = $corner.t.l #x corner.t.r$
#let subs = $subset.eq$
#let setminus = $backslash$
#let proves = $tack.r$
#let provesnot = $cancel(tack.r, length: #110%)$
#let modelsnot = $cancel(models, length: #90%)$
#let mreduc = $attach(<=, br: m)$
#let tred = $attach(<=, br: t)$
#let chl = $chevron.l$
#let chr = $chevron.r$
#let precc = $prec.eq$


// ── Computability / logic ────────────────────
#let add = $mono("add")$
#let mult = $mono("mult")$
#let fact = $mono("fact")$
#let Mm = $frak(M)$
#let Nn = $frak(N)$


// ── Algebra (import selectively if needed) ───
#let gl = $"GL"$
#let sl = $"SL"$
#let gln = $G L_n$
#let aut = $A u t$
#let Sym = $"Sym"$
#let span = $"span"$
#let ord = $"ord"$
#let inv = $""^(-1)$
#let eqh = $scripts(equiv)_H$


// ── Calligraphic letters ─────────────────────
#let aA = $cal(A)$; #let bB = $cal(B)$; #let cC = $cal(C)$; #let dD = $cal(D)$
#let eE = $cal(E)$; #let fF = $cal(F)$; #let gG = $cal(G)$; #let hH = $cal(H)$
#let iI = $cal(I)$; #let jJ = $cal(J)$; #let kK = $cal(K)$; #let lL = $cal(L)$
#let mM = $cal(M)$; #let nN = $cal(N)$; #let oO = $cal(O)$; #let pP = $cal(P)$
#let qQ = $cal(Q)$; #let rR = $cal(R)$; #let sS = $cal(S)$; #let tT = $cal(T)$
#let uU = $cal(U)$; #let vV = $cal(V)$; #let wW = $cal(W)$; #let xX = $cal(X)$
#let yY = $cal(Y)$; #let zZ = $cal(Z)$


// ── Bold vectors ─────────────────────────────
#let aa = $bold(a)$; #let bb = $bold(b)$; #let cc = $bold(c)$; #let dd = $bold(d)$
#let ee = $bold(e)$; #let ff = $bold(f)$; #let gg = $bold(g)$; #let hh = $bold(h)$
#let ii = $bold(i)$; #let jj = $bold(j)$; #let kk = $bold(k)$; #let ll = $bold(l)$
#let mm = $bold(m)$; #let nn = $bold(n)$; #let oo = $bold(o)$; #let pp = $bold(p)$
#let qq = $bold(q)$; #let rr = $bold(r)$; #let ss = $bold(s)$; #let tt = $bold(t)$
#let uu = $bold(u)$; #let vv = $bold(v)$; #let ww = $bold(w)$; #let xx = $bold(x)$
#let yy = $bold(y)$; #let zz = $bold(z)$


#let CSPACE = $sans("CSPACE")$
#let SPACE(..args) = $sans("SPACE")(#args-join(args))$
#let PrCatCSPACE(..args) = $PP_sans("Cat")sans("CSPACE")(#args-join(args))$
#let PPCat = $PP_sans("Cat")$
#let PPCatCL(..args) = $PP_sans("Cat")sans("CL")[#args-join(args)]$
#let CL = $sans("CL")$
#let ZP = $sans("ZP")$
#let CLP = $sans("CLP")$
#let CAT = $sans("Cat")$
#let Ps = $sans("P")$
#let EcatLCL = $EE_#CAT sans("LCL")[O(1)]$

// ── Reversibility ────────────────────────────
#let start = $"start"$
#let up = $arrow.t$
#let down = $arrow.b$
