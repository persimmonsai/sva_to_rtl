"""
State Machine Generator for SVA to RTL Translation

This module generates finite state machines from parsed SVA assertions.
"""

from typing import Dict, List, Set, Optional, Tuple, Any
from dataclasses import dataclass
from enum import Enum
import re

from .parser import SVAAssertion, SVASequence, SVAProperty, SVAOperator


class StateType(Enum):
    """State machine state types"""
    IDLE = "idle"
    ACTIVE = "active"
    SUCCESS = "success"
    FAILURE = "failure"
    WAIT = "wait"


@dataclass
class State:
    """Represents a state in the state machine"""
    name: str
    state_type: StateType
    condition: Optional[str] = None
    delay: int = 0
    next_states: List[str] = None
    
    def __post_init__(self):
        if self.next_states is None:
            self.next_states = []


@dataclass
class Transition:
    """Represents a transition between states"""
    from_state: str
    to_state: str
    condition: str
    action: Optional[str] = None


@dataclass
class StateMachine:
    """Represents a complete state machine"""
    name: str
    states: Dict[str, State]
    transitions: List[Transition]
    initial_state: str
    clock: str
    reset: Optional[str] = None
    disable_condition: Optional[str] = None
    signals: Set[str] = None
    
    def __post_init__(self):
        if self.signals is None:
            self.signals = set()


class StateMachineGenerator:
    """Generates state machines from SVA assertions"""
    
    def __init__(self):
        self.state_machines: Dict[str, StateMachine] = {}
        self.state_counter = 0
    
    def generate(self, assertion: SVAAssertion) -> StateMachine:
        """Generate a state machine from an SVA assertion"""
        self.state_counter = 0
        
        # Create state machine name
        sm_name = f"{assertion.name}_checker"
        
        # Extract clock and reset
        clock = self._get_clock(assertion)
        reset = self._get_reset(assertion)
        disable_condition = self._get_disable_condition(assertion)
        
        # Parse the sequence expression
        states, transitions, signals = self._parse_sequence_expression(
            assertion.property.sequence.expression
        )
        
        # Add initial idle state
        idle_state = State(
            name="IDLE",
            state_type=StateType.IDLE,
            condition=None
        )
        states["IDLE"] = idle_state
        
        # Add success and failure states for assertions
        if assertion.property.property_type == "assert":
            success_state = State(
                name="SUCCESS",
                state_type=StateType.SUCCESS
            )
            failure_state = State(
                name="FAILURE",
                state_type=StateType.FAILURE
            )
            states["SUCCESS"] = success_state
            states["FAILURE"] = failure_state
        
        # Create the state machine
        sm = StateMachine(
            name=sm_name,
            states=states,
            transitions=transitions,
            initial_state="IDLE",
            clock=clock,
            reset=reset,
            disable_condition=disable_condition,
            signals=signals
        )
        
        self.state_machines[sm_name] = sm
        return sm
    
    def _parse_sequence_expression(self, expression: str) -> Tuple[Dict[str, State], List[Transition], Set[str]]:
        """Parse a sequence expression into states and transitions"""
        states = {}
        transitions = []
        signals = set()
        
        # Tokenize the expression
        tokens = self._tokenize_expression(expression)
        
        # Parse tokens into state machine components
        current_state = "IDLE"
        
        for i, token in enumerate(tokens):
            if self._is_signal(token):
                # Signal condition
                signals.add(token)
                next_state = self._get_next_state_name()
                
                # Create state for this condition
                state = State(
                    name=next_state,
                    state_type=StateType.ACTIVE,
                    condition=token
                )
                states[next_state] = state
                
                # Create transition
                transition = Transition(
                    from_state=current_state,
                    to_state=next_state,
                    condition=token
                )
                transitions.append(transition)
                
                current_state = next_state
                
            elif token.startswith("##"):
                # Delay operator
                delay_match = re.match(r'##(\d+)', token)
                if delay_match:
                    delay = int(delay_match.group(1))
                    
                    # Create delay states
                    for d in range(delay):
                        delay_state = self._get_next_state_name()
                        state = State(
                            name=delay_state,
                            state_type=StateType.WAIT,
                            delay=d + 1
                        )
                        states[delay_state] = state
                        
                        # Create transition
                        transition = Transition(
                            from_state=current_state,
                            to_state=delay_state,
                            condition="1'b1"  # Always true
                        )
                        transitions.append(transition)
                        
                        current_state = delay_state
                        
            elif token in ["|->"]:
                # Implication operator
                # Create success/failure conditions
                if i < len(tokens) - 1:
                    consequent = tokens[i + 1]
                    
                    # Success transition
                    success_transition = Transition(
                        from_state=current_state,
                        to_state="SUCCESS",
                        condition=consequent
                    )
                    transitions.append(success_transition)
                    
                    # Failure transition
                    failure_transition = Transition(
                        from_state=current_state,
                        to_state="FAILURE",
                        condition=f"!({consequent})"
                    )
                    transitions.append(failure_transition)
                    
                    if self._is_signal(consequent):
                        signals.add(consequent)
        
        return states, transitions, signals
    
    def _tokenize_expression(self, expression: str) -> List[str]:
        """Tokenize an SVA expression"""
        # Simple tokenizer - can be enhanced for more complex expressions
        tokens = []
        
        # Replace common operators with spaces for splitting
        expression = expression.replace("##", " ## ")
        expression = expression.replace("|->", " |-> ")
        expression = expression.replace("|=>", " |=> ")
        
        # Split by whitespace and filter empty strings
        raw_tokens = expression.split()
        
        for token in raw_tokens:
            if token.strip():
                tokens.append(token.strip())
        
        return tokens
    
    def _is_signal(self, token: str) -> bool:
        """Check if a token represents a signal"""
        # Simple heuristic: if it looks like a valid identifier and not an operator
        operators = ["##", "|->", "|=>", "and", "or", "not", "throughout", "within"]
        
        if token in operators:
            return False
        
        # Check if it looks like a valid SystemVerilog identifier
        if re.match(r'^[a-zA-Z_][a-zA-Z0-9_]*(?:\[[^\]]+\])?$', token):
            return True
        
        # Check for expressions like (a && b)
        if token.startswith('(') and token.endswith(')'):
            return True
        
        return False
    
    def _get_next_state_name(self) -> str:
        """Generate next state name"""
        self.state_counter += 1
        return f"S{self.state_counter}"
    
    def _get_clock(self, assertion: SVAAssertion) -> str:
        """Extract clock signal"""
        # Check property first, then sequence
        if assertion.property.clock:
            return assertion.property.clock
        
        if assertion.property.sequence.clock:
            return assertion.property.sequence.clock
        
        # Default clock
        return "clk"
    
    def _get_reset(self, assertion: SVAAssertion) -> Optional[str]:
        """Extract reset signal"""
        # Check property first, then sequence
        if assertion.property.reset:
            return assertion.property.reset
        
        if assertion.property.sequence.reset:
            return assertion.property.sequence.reset
        
        return None
    
    def _get_disable_condition(self, assertion: SVAAssertion) -> Optional[str]:
        """Extract disable condition"""
        # Check property first, then sequence
        if assertion.property.disable_condition:
            return assertion.property.disable_condition
        
        if assertion.property.sequence.disable_condition:
            return assertion.property.sequence.disable_condition
        
        return None
    
    def generate_multiple(self, assertions: List[SVAAssertion]) -> Dict[str, StateMachine]:
        """Generate state machines for multiple assertions"""
        result = {}
        
        for assertion in assertions:
            try:
                sm = self.generate(assertion)
                result[sm.name] = sm
            except Exception as e:
                print(f"Warning: Failed to generate state machine for {assertion.name}: {e}")
        
        return result
    
    def optimize_state_machine(self, sm: StateMachine) -> StateMachine:
        """Optimize the state machine by removing redundant states"""
        # Simple optimization: remove unreachable states
        reachable_states = set()
        queue = [sm.initial_state]
        
        while queue:
            current = queue.pop(0)
            if current in reachable_states:
                continue
            
            reachable_states.add(current)
            
            # Find all states reachable from current
            for transition in sm.transitions:
                if transition.from_state == current:
                    queue.append(transition.to_state)
        
        # Remove unreachable states
        optimized_states = {name: state for name, state in sm.states.items() 
                          if name in reachable_states}
        
        # Remove transitions to/from unreachable states
        optimized_transitions = [t for t in sm.transitions 
                               if t.from_state in reachable_states and t.to_state in reachable_states]
        
        # Create optimized state machine
        optimized_sm = StateMachine(
            name=sm.name,
            states=optimized_states,
            transitions=optimized_transitions,
            initial_state=sm.initial_state,
            clock=sm.clock,
            reset=sm.reset,
            disable_condition=sm.disable_condition,
            signals=sm.signals
        )
        
        return optimized_sm
    
    def print_state_machine(self, sm: StateMachine):
        """Print state machine details for debugging"""
        print(f"State Machine: {sm.name}")
        print(f"Clock: {sm.clock}")
        print(f"Reset: {sm.reset}")
        print(f"Disable: {sm.disable_condition}")
        print(f"Initial State: {sm.initial_state}")
        print(f"Signals: {sm.signals}")
        
        print("\nStates:")
        for name, state in sm.states.items():
            print(f"  {name}: {state.state_type} (condition: {state.condition})")
        
        print("\nTransitions:")
        for transition in sm.transitions:
            print(f"  {transition.from_state} -> {transition.to_state} (condition: {transition.condition})")
        
        print()
    
    def get_state_machines(self) -> Dict[str, StateMachine]:
        """Get all generated state machines"""
        return self.state_machines
