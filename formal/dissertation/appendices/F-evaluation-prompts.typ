#import "../layout.typ": *

// Appendix F: Evaluation Prompts
#heading(level: 1)[Appendix F: Evaluation Prompts]

This appendix provides the complete prompt templates used for the empirical evaluation in Chapter 14. These prompts instruct LLMs to output CLAIR-formatted reasoning traces.

#heading(level: 2)[F.1 GSM8K Prompts]

#heading(level: 3)[F.1.1 System Prompt]

You are CLAIR-MATH, a mathematical reasoning system that outputs structured reasoning traces with explicit confidence scores, justifications, and invalidation conditions.

#heading(level: 3)[F.1.2 Task Instruction]

Solve the following grade school math problem step-by-step. For each step, output:

#block(
  fill: academic-cream,
  stroke: 1pt + academic-navy,
  inset: 10pt,
  radius: 3pt,
  [
    #set text(font: "Monaco", size: 9pt, fill: black)
    Step N: BELIEF("description of reasoning step", c=X.XX, justification="why this step is valid", invalidation="what would make this step false")
  ],
)

#strong[Confidence Guidelines:]
- c=1.00 for mathematical certainties (e.g., "3 + 5 = 8")
- c=0.95-0.99 for direct inferences from problem statement
- c=0.80-0.94 for multi-step calculations
- c=0.60-0.79 for assumptions about implicit information
- c=0.40-0.59 for uncertain interpretations

#strong[Justification Guidelines:]
- Reference explicit premises from the problem
- Reference previous step numbers when building on them
- State the mathematical operation being performed

#strong[Invalidation Guidelines:]
- State what condition would make this step incorrect
- Be specific: "if the problem meant X instead of Y"

#strong[Confidence Operations:]
- Multiply confidences when steps are chained: c_new = c_1 × c_2 × ...
- Use ⊕ (oplus) when combining independent sources: c = (c_1 + c_2) / 2
- Apply undercut when discovering contradictions: c_new = c × (1 - defeat_strength)

#heading(level: 3)[F.1.3 Few-Shot Example]

#block(
  fill: academic-cream,
  stroke: 1pt + academic-navy,
  inset: 10pt,
  radius: 3pt,
  [
    #set text(font: "Monaco", size: 8pt, fill: black)
    #strong[Problem:] Janet's ducks lay 16 eggs per day. She eats 3 for breakfast every morning and bakes muffins with 4 eggs every day. How many eggs does she have left at the end of the day?

    Step 1: BELIEF("Janet's ducks lay 16 eggs per day", c=1.00, justification="explicit premise in problem", invalidation="none - stated as fact")

    Step 2: BELIEF("Janet eats 3 eggs for breakfast", c=1.00, justification="explicit premise in problem", invalidation="none - stated as fact")

    Step 3: BELIEF("Janet bakes with 4 eggs", c=1.00, justification="explicit premise in problem", invalidation="none - stated as fact")

    Step 4: BELIEF("Total eggs used = eggs eaten + eggs baked", c=0.99, justification="arithmetic principle: total consumption", invalidation="if 'bakes' doesn't mean 'uses all eggs'")

    Step 5: BELIEF("Total eggs used = 3 + 4 = 7", c=0.99, justification="arithmetic: 3 + 4 = 7 using Steps 2,3", invalidation="none - basic addition")

    Step 6: BELIEF("Eggs remaining = eggs laid - eggs used", c=0.99, justification="arithmetic principle: remaining = initial - used", invalidation="if she also uses eggs for other purposes")

    Step 7: BELIEF("Eggs remaining = 16 - 7 = 9", c=0.99 × 0.99 × 0.99 = 0.97, justification="arithmetic: 16 - 7 = 9 using Steps 1,4,5,6", invalidation="none - basic subtraction")

    #strong[ANSWER:] 9 eggs (confidence: 0.97)
  ],
)

#heading(level: 3)[F.1.4 Test Prompt Template]

#block(
  fill: academic-cream,
  stroke: 1pt + academic-navy,
  inset: 10pt,
  radius: 3pt,
  [
    #set text(font: "Monaco", size: 9pt, fill: black)
    Solve the following math problem using the CLAIR format shown above:

    #strong[Problem:] {PROBLEM_TEXT}

    Provide your reasoning in the CLAIR format with confidence scores, justifications, and invalidation conditions.
  ],
)

#heading(level: 2)[F.2 HotpotQA Prompts]

#heading(level: 3)[F.2.1 System Prompt]

You are CLAIR-QA, a question answering system that builds justification graphs for multi-hop reasoning.

#heading(level: 3)[F.2.2 Task Instruction]

Answer the following question by reasoning over the provided context. Build a justification DAG where each step may depend on multiple previous steps.

#block(
  fill: academic-cream,
  stroke: 1pt + academic-navy,
  inset: 10pt,
  radius: 3pt,
  [
    #set text(font: "Monaco", size: 9pt, fill: black)
    Step N: BELIEF("intermediate conclusion", c=X.XX, justification="using entity E from passage P", support=[Step i, Step j, ...])
  ],
)

#strong[Support Guidelines:]
- `support=[i, j, ...]` lists which previous steps this step builds on
- Multiple support indicates the step requires all those premises
- This forms the justification DAG structure

#strong[Confidence for Multi-Hop Reasoning:]
- c=1.00 for direct entity extraction from passages
- c=0.90-0.95 for single-hop inferences (bridging entities)
- c=0.70-0.85 for multi-hop chains (multiply per hop: 0.90^n for n hops)
- c=0.60-0.75 for synthesizing across multiple passages

#strong[Defeat Operations:]
- When passages contradict, apply undercut: c_new = c × (1 - contradiction_strength)
- When answering multi-part questions, use rebut to compare alternatives

#heading(level: 3)[F.2.3 Few-Shot Example]

#block(
  fill: academic-cream,
  stroke: 1pt + academic-navy,
  inset: 10pt,
  radius: 3pt,
  [
    #set text(font: "Monaco", size: 8pt, fill: black)
    #strong[Question:] Were Scott Derrickson and Ed Wood of the same nationality?

    #strong[Passage 1:] Scott Derrickson (born May 16, 1966) is an American film director.

    #strong[Passage 2:] Ed Wood (1924-1978) was an American filmmaker.

    Step 1: BELIEF("Scott Derrickson is American", c=1.00, justification="direct extraction from Passage 1", support=[])

    Step 2: BELIEF("Ed Wood is American", c=1.00, justification="direct extraction from Passage 2", support=[])

    Step 3: BELIEF("American refers to nationality of United States", c=0.99, justification="background knowledge", support=[])

    Step 4: BELIEF("Both are American nationality", c=1.00 × 1.00 = 1.00, justification="both share nationality from Steps 1,2", support=[1, 2])

    Step 5: BELIEF("Therefore they are of the same nationality", c=1.00, justification="identity from same nationality value using Steps 3,4", support=[3, 4])

    #strong[ANSWER:] Yes (confidence: 1.00)
  ],
)

#heading(level: 3)[F.2.4 Test Prompt Template]

#block(
  fill: academic-cream,
  stroke: 1pt + academic-navy,
  inset: 10pt,
  radius: 3pt,
  [
    #set text(font: "Monaco", size: 9pt, fill: black)
    Answer the following question using the CLAIR format:

    #strong[Question:] {QUESTION}

    #strong[Context Passages:]
    {PASSAGES}

    Build your answer as a justification DAG with explicit support dependencies.
  ],
)

#heading(level: 2)[F.3 FOLIO Prompts]

#heading(level: 3)[F.3.1 System Prompt]

You are CLAIR-LOGIC, a logical reasoning system that handles first-order logic with defeasible reasoning and belief revision.

#heading(level: 3)[F.3.2 Task Instruction]

Determine whether the conclusion follows from the premises. Use CLAIR to track logical uncertainty and apply defeat operations when arguments are undermined.

#block(
  fill: academic-cream,
  stroke: 1pt + academic-navy,
  inset: 10pt,
  radius: 3pt,
  [
    #set text(font: "Monaco", size: 9pt, fill: black)
    Step N: BELIEF("logical derivation", c=X.XX, justification="rule application: Modus Ponens/Universal Instantiation/etc", defeat=[defeater description if applicable])
  ],
)

#strong[Logical Confidence Levels:]
- c=1.00 for logically necessary deductions (Modus Ponens from certainties)
- c=0.90-0.95 for probabilistic inferences from existential quantifiers
- c=0.70-0.85 for defeasible generalizations
- c=0.50-0.70 for abductive inferences (inference to best explanation)

#strong[Defeat in Logical Reasoning:]
- `undercut`: Attack the connection between premise and conclusion
- `rebut`: Provide a contradictory conclusion
- `rebuttal`: Attack an attacking argument

#strong[Self-Reference Detection:]
- When a conclusion refers to itself, apply graded Löb discount: g(c) = c²
- This prevents overconfident self-bootstrapping

#heading(level: 3)[F.3.2 Few-Shot Example]

#block(
  fill: academic-cream,
  stroke: 1pt + academic-navy,
  inset: 10pt,
  radius: 3pt,
  [
    #set text(font: "Monaco", size: 8pt, fill: black)
    #strong[Premises:]
    1. All doctors are college graduates.
    2. All cardiologists are doctors.
    3. John is a cardiologist.
    4. Some college graduates are not medical professionals.

    #strong[Conclusion:] John is a medical professional.

    Step 1: BELIEF("∀x (Doctor(x) → CollegeGraduate(x))", c=1.00, justification="Premise 1 as logical axiom", defeat=[])

    Step 2: BELIEF("∀x (Cardiologist(x) → Doctor(x))", c=1.00, justification="Premise 2 as logical axiom", defeat=[])

    Step 3: BELIEF("Cardiologist(John)", c=1.00, justification="Premise 3 as fact", defeat=[])

    Step 4: BELIEF("Doctor(John)", c=1.00, justification="Modus Ponens: Cardiologist(John) ∧ ∀x(Cardiologist→Doctor) ⊢ Doctor(John) using Steps 2,3", defeat=[])

    Step 5: BELIEF("CollegeGraduate(John)", c=1.00, justification="Modus Ponens: Doctor(John) ∧ ∀x(Doctor→CollegeGraduate) ⊢ CollegeGraduate(John) using Steps 1,4", defeat=[])

    Step 6: BELIEF("MedicalProfessional is a superset of Doctor", c=0.95, justification="defeasible generalization: doctors are medical professionals", defeat=[])

    Step 7: BELIEF("MedicalProfessional(John)", c=1.00 × 0.95 = 0.95, justification="instantiation: Doctor(John) implies MedicalProfessional(John) using Steps 4,6", defeat=[])

    Step 8: BELIEF("Conclusion follows", c=0.95, justification="derivation chain supports conclusion", defeat=[])

    #strong[ANSWER:] True (confidence: 0.95)
  ],
)

#heading(level: 3)[F.3.3 Defeat Example]

#block(
  fill: academic-cream,
  stroke: 1pt + academic-navy,
  inset: 10pt,
  radius: 3pt,
  [
    #set text(font: "Monaco", size: 8pt, fill: black)
    #strong[Premises:]
    1. Birds typically fly.
    2. Tweety is a bird.
    3. Tweety is a penguin.
    4. Penguins cannot fly.

    #strong[Conclusion:] Tweety cannot fly.

    Step 1: BELIEF("Tweety flies", c=0.80, justification="defeasible generalization: birds fly using Premises 1,2", defeat=[])

    Step 2: BELIEF("The generalization 'birds fly' has exceptions", c=1.00, justification="background knowledge", defeat=[])

    Step 3: BELIEF("Penguins are exceptions to 'birds fly'", c=1.00, justification="Premise 4 + background knowledge", defeat=[])

    Step 4: BELIEF("Tweety is a penguin", c=1.00, justification="Premise 3", defeat=[])

    Step 5: BELIEF("UNDERCUT: 'birds fly' generalization doesn't apply to Tweety", c=1.00, justification="specific overrides general: penguin Tweety using Steps 3,4", defeat=["attacks Step 1"])

    Step 6: BELIEF("Tweety cannot fly (rebuttal to Step 1)", c=1.00, justification="penguins cannot fly using Premise 4", defeat=["rebutts Step 1"])

    Step 7: BELIEF("Tweety cannot fly", c=1.00, justification="specific fact overrides defeasible generalization using Steps 5,6", defeat=[])

    #strong[ANSWER:] True (confidence: 1.00)

    #emph[Note:] This demonstrates defeasible reasoning: a specific fact (Tweety is a penguin) defeats a defeasible generalization (birds fly).
  ],
)

#heading(level: 3)[F.3.4 Test Prompt Template]

#block(
  fill: academic-cream,
  stroke: 1pt + academic-navy,
  inset: 10pt,
  radius: 3pt,
  [
    #set text(font: "Monaco", size: 9pt, fill: black)
    Determine if the conclusion follows from the premises using CLAIR logical reasoning:

    #strong[Premises:]
    {PREMISES}

    #strong[Conclusion:] {CONCLUSION}

    Apply defeat operations when premises create contradictory or undercutting relationships.
  ],
)

#heading(level: 2)[F.4 Post-Processing and Validation]

#heading(level: 3)[F.4.1 Confidence Extraction]

For baseline methods, confidence is extracted as follows:

#strong[Chain-of-Thought / Tree of Thoughts / DSPy:]
```python
confidence = max(logprob(token) for token in answer_tokens)
# Normalize to [0,1]
confidence = sigmoid(confidence / temperature)
```

#strong[Self-Consistency:]
```python
confidence = (count_agreeing / total_samples)
# Voting proportion as confidence
```

#strong[CLAIR:]
```python
# Extract final confidence from CLAIR trace
confidence = trace[-1]['confidence']
# Already normalized to [0,1]
```

#heading(level: 3)[F.4.2 Validation Checklist]

For each CLAIR output, verify:

1. #strong[Format correctness:] All BELIEF statements have c, justification, and invalidation/defeat
2. #strong[Confidence bounds:] All c values are in [0, 1]
3. #strong[Justification structure:] Support dependencies form a DAG (no cycles unless intentional)
4. #strong[Confidence calculus:] Multiplication for chains, ⊕ for independent evidence
5. #strong[Defeat application:] Undercut/rebut applied correctly when contradictions arise
6. #strong[Self-reference discount:] Graded Löb applied (c²) for self-referential beliefs

#heading(level: 3)[F.4.3 Error Categories for Annotation]

When evaluating CLAIR outputs, categorize errors as:

#strong[C1: Syntax errors.] Invalid CLAIR format, missing confidence/justification fields

#strong[C2: Confidence miscalibration.] Confidence doesn't match logical strength of derivation

#strong[C3: Invalid confidence propagation.] Using ⊕ for dependent sources, incorrect multiplication

#strong[C4: Missing justification dependencies.] DAG doesn't include necessary support links

#strong[C5: Incorrect defeat application.] Using rebut when undercut is appropriate (or vice versa)

#strong[C6: Unjustified independence assumption.] Applying ⊕ to correlated sources

#strong[C7: Self-reference bootstrapping.] Circular reasoning without graded Löb discount

#strong[C8: Semantic errors.] Reasoning step is logically invalid regardless of CLAIR structure
