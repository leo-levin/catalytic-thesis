#import "preamble.typ": *
#show: init.with(title: "Leo Frankel Thesis Proposal")
#let bin = $"bin"$
#let cc = $compose$
#let HALT = $"HALT"_"TM"$
#let ACC = $"A"_"TM"$
#let m(content) = $mono("content")$



\
*Name:*			Leo Frankel\

*Student ID:*		12388352\

*Bx Thesis Advisor:*	Janos Simon\

*Second Reader:* _to do_

*Thesis Title:*		_ Space-Bounded and Catalytic Computation_\

*Proposal:*

=== Background
In catalytic computation @BCKLS14, a space-bounded machine has, in addition to its work tape, a large catalytic tape with arbitrary initial contents, which it must restore exactly before halting. We write $sans("CSPACE")(s, c)$ for the class of languages decidable by such machines with $s$ bits of work space and $c$ bits of catalytic space, where $c$ is usually taken to be at most $2^(O(s))$. Despite the restoration constraint, the catalytic tape adds power: catalytic logspace, $sans("CL") = sans("CSPACE")(O(log n), "poly"(n))$, satisfies $sans("TC")^1 subs sans("CL") subs sans("ZPP")$ @BCKLS14. So $sans("CL")$ contains problems not known to be in logspace, yet remains within randomized polynomial time.

Catalytic techniques have also proved useful outside the catalytic setting. Cook and Mertz used them to show that Tree Evaluation is in space $O(log n dot log log n)$ @CM20 @CM21 @CM25, and Williams built on this result to simulate time $t$ in space $O(sqrt(t log t))$ @Wil25. Understanding where the power of the catalytic tape comes from may therefore also inform ordinary space-bounded computation. Not that my results (if I have results) would be such momentous leaps, but just in that the catalytic regime is something worth studying.

I want to study which features of the catalytic model this added power depends on, and what happens when these features are relaxed or restricted. The most natural is the requirement that the catalytic tape be restored exactly. Others include how much ordinary work space the machine is given alongside its catalytic tape, and how the model behaves at the extremes of its parameters. I may also like to explore connections between catalytic computation and related models, such as space-bounded probabilistic transducers whose output may be rewritten or non-regular languages in $o(log log n)$ workspace.

=== Relaxing restoration
How much of the catalytic tape's power depends on its being restored exactly? Lossy catalytic computation, in which the machine may leave a bounded number of bit errors on the catalytic tape, has been fully characterized @GJST24 @FMST25. Koucký, Mertz, and Sami @KMS26 extend this line of work to other kinds of resetting error, organized along two axes: whether the tape may be left unrestored or may have some expected number of bit errors, and whether this failure is measured over the machine's random bits or over the initial contents of the tape. Of the four resulting combinations, they define three:

#figure(
  table(
    columns: 3,
    align: center + horizon,
    inset: 7pt,
    stroke: 0.5pt,
    table.header([], [*Over the random bits*], [*Over the initial tape*]),
    [*Tape may be destroyed*], $sans("BP")^(epsilon)sans("C")^delta sans("SPACE")(s,c)$, [*–––*],
    [*Expected bit errors*], $EE_(sans("Rand"))sans("BPLCSPACE")(s,c,e)$, $EE_(sans("Cat"))sans("LCSPACE")(s,c,e)$,
  ),
) <tab:robust>

These three classes, @KMS26 suggest, “seem to capture all remaining natural models of resetting error”. Presumably, they find defining the fourth class unnecessary, as it will likely be equivalent to one of the other three classes. Nonetheless, to complete the table, we define this class: languages decidable by deterministic catalytic machines that always answer correctly and, on every input, restore the catalytic tape exactly on at least a $1-delta$ fraction of initial contents. On the remaining contents, the tape may be destroyed. We call this class $PP_(sans("Cat"))sans("CSPACE")(s,c,delta)$, for _probably_ catalytic.

At the extremes, this class is easy to describe. When $delta = 0$, the tape must always be restored, giving $sans("CSPACE")(s,c)$; when $delta = 1$, it never needs to be restored, giving $sans("SPACE")(O(s+c))$. So $delta$ is a single parameter running from catalytic to ordinary space, along which other catalytic classes might be placed. I do expect $PP_(sans("Cat"))sans("CSPACE")$ to collapse as @KMS26 predict, but which class it collapses to should depend on $delta$. I want to understand which classes appear between these endpoints, and where along $delta$ the class changes.

A related question is what exact restoration costs. Given a probably-catalytic machine, how much additional work space is needed to turn it into one that always restores its tape? Extra work space and a looser restoration requirement seem to be interchangeable. Roughly, I think, each additional bit of work space seems to be worth halving the fraction of initial tapes that must be restored.



=== Small workspace
Most work on catalytic computation concerns the logspace setting. I would also like to look at what a catalytic tape can do when the work space is very small. For ordinary TMs it is known that, with less than roughly $log log n$ work space, a machine can recognize only regular languages.

A natural question is whether having the catalytic tape changes this bound. That is, whether a machine with $o( log log n)$  work space but a larger catalytic tape can recognize a non-regular language. The usual proof works by bounding the number of configurations the machine can be in as its input head moves ("crossing sequences"). A catalytic machine has far more configurations, but it must restore the tape by the end, so the average number of feasible configurations is smaller. It is not clear whether this requirement limits it enough for a similar argument to go through. More broadly, I am interested in how the power of the catalytic tape changes as the work space shrinks.


=== Other questions
*Probabilistic transducers.* A space-bounded probabilistic machine with a write-once output tape can be simulated deterministically in quadratic space. Both this model and catalytic machines have a large number of possible configurations, but a far more limited number of actually usable/reachable configurations. Is there a similar simulation when the output may be rewritten?

*Detecting changes to the tape.* Instead of restoring the catalytic tape, how much work space does a machine need just to check whether the tape has been changed?

*Restoring on a fixed set of tapes.* Almost-catalytic machines @BDRS25 need only restore tapes in a fixed set $A$. How do they compare to probably-catalytic machines, where only the size of the restored set is constrained?

*Reversibility.* Ordinary and catalytic machines can be made reversible without extra space, and this extends to catalytic machines with errors @Lan00 @Dul15 @GJST24. Can probably-catalytic machines be made reversible in the same way?

*Smaller catalytic tapes.* Most results assume a catalytic tape of size up to $2^(O(s))$. How do these models behave when the catalytic tape is much smaller, for example polynomial in the work space?

*Time bounds.* @KMS26 find that adding a polynomial time bound change how some of their classes relate. Does the same happen for probably-catalytic machines?

=== Work so far
So far I have begun to read the main papers on catalytic and robust catalytic computation @BCKLS14 @GJST24 @FMST25 @CLMP25 @KMS26, and worked through some of the configuration-graph and reversibility techniques they rely on @Lan00 @Dul15 @CLMP25.

I have formalized a definition of $PP_(sans("Cat"))sans("CSPACE")$ and its behavior at $delta = 0$ and $delta = 1$. I have also sketched two preliminary arguments. First, a probably-catalytic machine can be made to always restore its tape using roughly $log(delta 2^c)$ extra bits of work space, by walking its configuration graph and counting the starting configurations it passes. Second, in the logspace setting, for most values of $delta$ the class appears to coincide with zero-error catalytic logspace, $sans("ZP")_(sans("Cat"))sans("CL")$.


=== Bibliography / Reading List
#bibliography("refs.bib", style: "alpha.csl", full: true, title: none)


\

#box(stroke: 1pt, outset: 10pt)[
  _AI Usage: I used my university-provided Claude subscription to help me find papers, write citations, and as a proofreader._

  I have also worked on this proposal as part of WRIT 33000: Academic and Professional Writing (Little Red Schoolhouse), a class I am currently enrolled in.
]
