**Group 1 (15-25 min)**
- disjunction exercise where you can prove both
- confused by \andI notation, clarify "I" stands for introduction rule (we may change the notation to make game more self-contained; keep for now maybe remove later)

- too much hand holding, not feeling as much learning (but maybe necessary since this is like tutorial/exposition; can have explicit directions in first few levels as to not get discouraged but wean them off of it later)

- interested in freedom to make your own proofs

- initially trying to drag like code blocks, "by typing and pressing enter" is clearer (world 0)

- fill in documentation - more explanation of syntax
(docs: examples)

rohan: maybe explain how symbols are typed in latex/lean when introduced (`\and`)

- emphasizing difference between assumptions and goals and where they appear in the game interface (disconnection was in what specific words are used)

**Group 2 (1 hr)**
feature wishlist:
- ability to change which goal is active; weird that you can solve active goal while viewing the second goal

other comments:
- nice that first few levels are simple math since students are simultaneously learning lean syntax
- kinda wish we could change names of tactics to what is intuitive to us (imp is unnatural)
- like the feeling of earning theorems

can fix:
- for `or_intro 3<2`, give some text to say that student must go back because impossible to prove
- unfold Not
- clarify whether our game is standalone or supplement; why take \andI syntax but not specify definition numbers so students can read more / reference book
- formatting: boxes end mid-sentence
- world 0: if server crashes, reload page; switch to editor view
- documentation please (hard to remember purpose of each tactic, maybe the names `imp_elim` only helpful if you already know implication and elimination rules)
- explain left/right instead of typing entire complicated expression
- use words over notation to make clear when something is arbitrary and what is formal notation (h' could be interpreted as derivative, hold hand by replacing with h1 and noting "or whatever you named it")
- wording of last paragraph in level 5: assuming p is true means we add it as hypothesis, explicitly draw that connection
- make clearer elim modifies hypo and intro modifies goal; however, imp_elim modifying goal changes the philosophy
- neg being equivalent to implies false is not obviously same as thinking of negation as operator on booleans
- make rewrite tactic not have brackets

Assorted notes from test drive; K and W came this afternoon
W had issues with the naming conventions for tactics. Said that and_intro, or_intro, and iff_intro were fine. elim might be more elegantly phrased as split (I think this is a great idea), and imp_elim and imp_intro are confusing because there are existing math phrases in use; fix, assume, and apply might be better to use for those tactics specifically
K suggested having variants of or_intro that work like left and right, so that students don’t have to type out the whole disjunct if it is long and there are only 2
K was also confused by the naming schemes for the introduction/elimination rules
Various comments on UI; frankly I’ll put them off for now since I want to focus on content but we can discuss them if you guys want to
W liked having prepositions be part of the syntax for tactics, made them feel more natural
W seemed to go through the whole game without internalizing much, i.e. they did not know what some basic tactics did even after doing all of ch 1.1. (Although I would not expect someone to be fully comfortable at that point anyways).