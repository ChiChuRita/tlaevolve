- Postprocess TLC output
- Update user message to not include properties all the time
- How can we ensure the original skeleton program automatically has a bad score?
  - Maybe not use Line Error / Total Lines, but rather the absolute line? Then purposly have invaled syntax in the skeleton blueprint?
- Explain Score in SystemPrompt, so that model understands how to deal with that


# Syntax Check: Synticitcal Correctness could mislead to wrong implementations that just have correct syntax...
- Problem 1: Dummy Code added by the LLM (this could be modeled valid with a skip, leading to high score)
  - Possible Solution: Model dummy code as syntax location (advise LLM to do so)
- Problem 2: Relative score (Error line / Total lines) might be misleading, maybe the solution of a long program is correct, but it has a syntax error right at the end
  - Possible Solution: Use weightes average of Error and Length of Program
  - Pitfalls of Solution: We dont want to incentivice long programs to much
- Alternative Idea: Use LLM as a judge to assign score
- Ultimiate Soution (if possible): Have sophisticated prompt so that syntax errors wont happen!!!!