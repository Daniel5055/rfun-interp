
Could use a labelled transition system (S,N, ->, s0)

An individual state represents:

- A set of actors
- Each actor contains:
    - An inbox
    - A value
    - Command definition

Would also need an environment defining function and actor command definitions

Most labels would be empty except for the first label to set the value of the initial state main actor?
- Or alternatively all labels are empty, and the initial value is defined in the actor

- Then all that is left to define the transition function
    - where each step represents the evaluation of an individual valid actor, including the side effects it may cause 
    - Therefore I need to define the semantics of an individual actor's command definition being evaluated
    - The evaluation of a command definition should be 
    deterministic in both directions

- Also need to state how to determine if an actor is valid to have its command definition executed
    - Through comparing inbox to receives in command
    - Or through comparing send for reversible execution
        - In which case the command definition is reversed and executed
            - Therefore may need to define reversing semantics

- The transition function is not deteministic because in a single step, any valid actor could be executed


- To evaluate a command definition,
    - Need the inbox to receive messages
    - Need the value to modify
    - Need to access other a actors
        - Need the ability to add and remove actors
        - Need the ability to add messages and remove actors
            - New actors retrieved from actor command definition environment
    - So something like
        
        
```
env |- (cmd', v, [msgs], [a]) -> (cmd', v', [msgs'], [a'])
```

Alternatively is a denotational semantics to a process calculus