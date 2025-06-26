**June 19**
mechanics of proof by heather macbeth: https://hrmacbeth.github.io/math2001/

so far, have made and_intro, and_elim, or_intro, or_elim, imp_intro, imp_elim as macros/replacements for And.intro, left/right, use, cases, intro, apply, mostly so that naming conventions are consistent. when doing the negation levels, realized that intro and apply are very powerful, starting to think we might keep them as is. thoughts?
- have imp_intro and imp_elim in beginning, maybe have intro/apply/assume later on

plan: should we focus on refining ch.0-2 and test drive, then use as template to develop the rest of the content? thinking it is possible we decide to change something fundamental, like whether we stick with the "trivial" proofs or open up more of lean for students to use.
- finish 1.2 & 1.3 (will do quantifier tactics)
- finish ch.3 then ask hoskinson students, suami students, clive for feedback

**June 23**
tactic for using excluded middle
unfold neg to implication
contradiction ___ ___ tactic
simp in quantifiers and variable
maybe use rfl instead of trivial (combines rfl, contradiction)

new tactics:
unfold Not
excluded_middle
contradiction h1, h2

**June 24**
presentation today
future of the project
- everybody would like to continue to some degree
- should maybe push it out there, advertise that we're working on it so other people can use to teach or request changes

test driving this week (maybe ch. 0 & 1), snacks to watch live (all of ssp, suami, pre-college students?)
- game assumes some knowledge
- best testers are actual students, second best is suami, both kinds of feedback helpful

biconditional levels: elim being trivial, functional approach for intro rule (pic on phone)
- simparith
- can keep for now

sorryAx Prop true \imp y < y + 1 in forall_intro level

**June 25**
thoughts on lecture
test driving today/tmrw, share julian & orlando's feedback
offner's suggestion of detour worlds for more exercises
section 1.1/1.2 thoughts:
- should we do unfold Not for negation? (yes)
- might want to change `and_intro` name
- are we changing trivial? (separate trivial and contradiction, look into which tactics trivial runs, might get confused as to why trivial sometimes works and sometimes doesn't)
next: sections 1.2, 1.3, then revise ch.2 & 3