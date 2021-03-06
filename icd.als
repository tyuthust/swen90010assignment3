// ===========================================================================
// SWEN90010 2018 - Assignment 3 Submission
// by <Risheng Fang 749481
//     Yuchao Chen  767394>
// ===========================================================================

module ebs
open util/ordering[State] as ord

// =========================== System State ==================================
// a type for storing amounts of Joules
sig Joules {}

// the initial number of joules to deliver (30)
one sig InitialJoulesToDeliver extends Joules {}

// we ignore the clinical assistants for simplicity in this model 
abstract sig Role {}
one sig Cardiologist, Patient extends Role {}

// principals have associated roles
sig Principal {
  roles : set Role
}

// an abstract signature for network messages
abstract sig Message {
  source : Principal
}

// ChangeSettingsRequest messages
// Note: we ignore the tachybound part to keep things tractable
sig ChangeSettingsMessage extends Message {
  joules_to_deliver : Joules
}

// ModeOn message
sig ModeOnMessage extends Message {
}


// Modes: either On or Off
abstract sig Mode {}
one sig ModeOn, ModeOff extends Mode {}

// meta information in the model that identifies the last action performed
abstract sig Action {
  who : Principal  // indentifies which principal caused the action
}

sig SendModeOn, RecvModeOn,
    SendChangeSettings, RecvChangeSettings
    extends Action {}

// represents the occurrence of attacker actions
one sig AttackerAction extends Action {}

// a dummy action which will be the "last action" in the initial state
// we do this just to make sure that every state has a last action
one sig DummyInitialAction extends Action {}

// The system state
sig State {
  network : lone Message,              // CAN Bus state: holds up to one message
  icd_mode : Mode,                 // whether IXS system is in on or off mode
  impulse_mode : Mode,             // whether the impulse generator is on or off
  joules_to_deliver : Joules,      // joules to deliver for ventrical fibrillation
  authorised_card : Principal,     // the authorised cardiologist
  last_action : Action,            // identifies the most recent action performed
}

// an axiom that restricts the model to never allow more than one messasge on
// the network at a time; a simplifying assumption to ease the analysis
fact {
  all s : State | lone s.network
}

// =========================== Initial State =================================

// The initial state of the system:
//   - empty network, 
//   - ICD and impulse generator both off
//   - joules to deliver at initial value
//   - the authorised cardiologist is really a cardiologist
//   - last_action set to the dummy value
pred Init[s : State] {
  no s.network and s.icd_mode = ModeOff and s.impulse_mode = ModeOff 
  and s.joules_to_deliver = InitialJoulesToDeliver and 
  Cardiologist in s.authorised_card.roles and
  s.last_action = DummyInitialAction
}

//run Init for 2

// =========================== Actions =======================================

// Models the action in which a ModeOn message is sent on the network by the
// authorised cardiologist.
// Precondition: none
// Postcondition: network now contains a ModeOn message from the authorised 
//                cardiologist
//                last_action is SendModeOn for the message's sender
//                and nothing else changes
pred send_mode_on[s, s' : State] {
  some m : ModeOnMessage | m.source = s.authorised_card and
  s'.network = s.network + m and
  s'.icd_mode = s.icd_mode and
  s'.impulse_mode = s.impulse_mode and
  s'.joules_to_deliver = s.joules_to_deliver and
  s'.authorised_card = s.authorised_card and
  s'.last_action in SendModeOn and
  s'.last_action.who = m.source
}

// Models the action in which a valid ModeOn message is received by the
// ICD from the authorised cardiologist, causing the ICD system's mode to change 
// from Off to On and the message to be removed from the network
// Precondition: the network now contains a ModeOn message from the authorised 
//               cardiologist
//               --last_action is SendModeOn for the message's sender--
//               the current icd_mode and impulse_mode is Modeoff
// Postcondition: the current icd_mode and impulse_mode is set as ModeOn
//                last_action in RecvModeOn and 
//                last_action.who = the source of the ModeOn message
//                and nothing else changes
pred recv_mode_on[s, s' : State] {
  // s.last_action =  SendModeOn  and
  s.network in ModeOnMessage and
  s.network.source.roles = Cardiologist and
  s.icd_mode in ModeOff and
  s.impulse_mode in ModeOff and
  s'.icd_mode = ModeOn and
  s'.impulse_mode = ModeOn and
  no s'.network and
  s'.joules_to_deliver = s.joules_to_deliver and
  s'.authorised_card = s.authorised_card and
  s'.last_action in RecvModeOn and
  s'.last_action.who = s.network.source
}

// Models the action in which a valid ChangeSettingsRequest message is sent
// on the network, from the authorised cardiologist, specifying the new quantity of 
// joules to deliver for ventrical fibrillation.
// Precondition: none
// Postcondition: network now contains a ChangeSettings message from the authorised 
//                cardiologist
//                and the joules_to_deliver is set as a given value
//                last_action in SendChangeSettings and
//                last_action.who = the source of the ChangeSettingsMessage
//                and nothing else changes
pred send_change_settings[s, s' : State] {
  some m : ChangeSettingsMessage | m.source = s.authorised_card and 
  m.joules_to_deliver = (Joules-InitialJoulesToDeliver) and
  s'.network = s.network + m and
  s'.icd_mode = s.icd_mode and
  s'.impulse_mode = s.impulse_mode and
  s'.joules_to_deliver = s.joules_to_deliver and
  s'.authorised_card = s.authorised_card and
  s'.last_action in SendChangeSettings and
  s'.last_action.who = m.source
}

// Models the action in which a valid ChangeSettingsRequest message is received
// by the ICD, from the authorised cardiologist, causing the current joules to be 
// updated to that contained in the message and the message to be removed from the 
// network.
// Precondition: the current icd_mode and impulse_mode is set as ModeOff
//               the network now contains a ChangeSettings message from the authorised 
//               cardiologist
//               --last_action SendChangeSettings--
// Postcondition: joules to deliver is set as the given value
//                last_action in RecvChangeSettings and
//                last_action.who = the source of the ChangeSettingsMessage
//                and nothing else changes
pred recv_change_settings[s, s' : State] {
  //s.last_action = SendChangeSettings and
  s.icd_mode in ModeOff and 
  s.impulse_mode in ModeOff and
  s.network in ChangeSettingsMessage and
  s.network.source.roles in Cardiologist and
  s'.joules_to_deliver=s.network.joules_to_deliver and
  no s'.network and
  s'.icd_mode = s.icd_mode and
  s'.impulse_mode = s.impulse_mode and
  s'.last_action in RecvChangeSettings and
  s'.last_action.who = s.network.source
}

// =========================== Attacker Actions ==============================

// Models the actions of a potential attacker that has access to the network
// The only part of the system state that the attacker can possibly change
// is that of the network
//
// NOTE: In the initial template you are given, the attacker
// is modelled as being able to modify the network contents arbitrarily.
// However, for later parts of the assignment you will change this definition
// to only permit certain kinds of modifications to the state of the network.
// When doing so, ensure you update the following line that describes the
// attacker's abilities.
//
// Attacker's abilities: 1.delete the message network the network
//                       2.interfere the network by sending an unauthorized message
//                       3.repeat all previous messages
//                       4.modify the joules if the message is send joules message

// Precondition: none
// Postcondition: network state changes in accordance with attacker's abilities
//                last_action is AttackerAction
//                and nothing else changes
pred attacker_action[s, s' : State] {
  (
   (one s.network and no s'.network) 
    or (some m : Message {(m.source not in s.authorised_card and s'.network = m)}) 
    or (all previous : ord/prev[s'] | s'.network = previous.network) 
    or  (some j : Joules{s.network.joules_to_deliver = j and s'.network = s.network})
  ) and
  s'.icd_mode = s.icd_mode and
  s'.joules_to_deliver = s.joules_to_deliver and
  s'.impulse_mode = s.impulse_mode and
  s'.authorised_card = s.authorised_card and
  s'.last_action = AttackerAction and
  s'.last_action.who = s.network.source
}


// =========================== State Transitions and Traces ==================

// State transitions occur via the various actions of the system above
// including those of the attacker.
pred state_transition[s, s' : State] {
  send_mode_on[s,s']
  or recv_mode_on[s,s']
  or send_change_settings[s,s']
  or recv_change_settings[s,s']
  or attacker_action[s,s']
}

// Define the linear ordering on states to be that generated by the
// state transitions above, defining execution traces to be sequences
// of states in which each state follows in the sequence from the last
// by a state transition.
fact state_transition_ord {
  all s: State, s': ord/next[s] {
    state_transition[s,s'] and s' != s
  }
}

// The initial state is first in the order, i.e. all execution traces
// that we model begin in the initial state described by the Init predicate
fact init_state {
  all s: ord/first {
    Init[s]
  }
}

// run { last.icd_mode=ModeOn} for exactly 8 State, 2 Joules, 4 Action, 1 Principal, 2 Message
run { last.last_action=RecvChangeSettings} for exactly 7 State, 2 Joules, 4 Action, 2 Principal, 2 Message
// run { last.last_action=AttackerAction} for exactly 5 State, 3 Joules, 4 Action, 2 Principal, 2 Message

// =========================== Properties ====================================


// An example assertion and check:
// Specifies that once the ICD is in the On mode, it never leaves
// the On mode in all future states in the execution trace, 
// i.e. it stays in the On mode forever.
assert icd_never_off_after_on {
  all s : State | all s' : ord/nexts[s] | 
     s.icd_mode = ModeOn implies s'.icd_mode = ModeOn
}

check icd_never_off_after_on for 10 expect 0



// Describes a basic sanity condition of the system about how the modes of the
// ICD system and the impulse generator are related to each other. 
// This condition should be true in all states of the system, 
// i.e. it should be an "invariant"
pred inv[s : State] {
  (s.icd_mode = ModeOn) implies (s.impulse_mode = ModeOn)
}

// Specifies that the invariant "inv" above should be true in all states
// of all execution traces of the system
assert inv_always {
  inv[ord/first] and all s : ord/nexts[ord/first] | inv[s]
  // NOTE (as a curiosity): the above is equivalent to saying
  // all s : State | inv[s]
  // This is because when checking this assertion, the linear order
  // defined on States causes all States considered by Alloy to come
  // from the linear order
}

// Check that the invariant is never violated during 15
// state transitions
check inv_always for 15
// The assert always hold even with the 30 scope since the icd mode is turned on only 
// when impulse generator is on in 'recv_mode_on' predicate. 
// Even if there is AttackerAction, the assert still holds.
// Because the initial AttackerAction can only modify the content of network 
// but not change the information of the system, 
// such as icd_mode and impulse generator mode directly.
// In this way, the Rev_On_Pred can ignore the network content when it does not 
// equal the valid message.
// As a result, there will not be any message to turn the impulse generator off 
// while leaving icd on.


// An unexplained assertion. You need to describe the meaning of this assertion
// Specifies that when there is not any attacker action in the model, 
// the roles of the who of the RecvChangeSettings action should not be Paitent
assert unexplained_assertion {
  all s : State | (all s' : State | s'.last_action not in AttackerAction) =>
      s.last_action in RecvChangeSettings =>
      Patient not in s.last_action.who.roles
}

check unexplained_assertion for 5
// The assert always hold when the scope even if the scope is 15, so the model fails above assert check.
// the recv_change_settings method will never allow that the s.network.source.roles is Patient

// Check that the device turns on only after properly instructed to
// i.e. that the RecvModeOn action occurs only after a SendModeOn action has occurred
assert turns_on_safe {
  // For all State s and s' if s and s' form pred recv_mode_on
  // it should be that previous state of s and s form pred send_mode_on
  all s,s' : State|
  recv_mode_on[s,s']=>send_mode_on[ord/prev[s],s]
}

// NOTE: you may want to adjust these thresholds for your own use
check turns_on_safe for 5 but 8 State

// assert change_setting_safe {
//   all s,s' : State|
//     (recv_change_settings[s,s'] and attacker_action[ord/prev[s],s]) => 
//     s'.joules_to_deliver = s.joules_to_deliver
// }
// check change_setting_safe for 5 but 8 State



// assert attack_detect

// <Question: does the assertion hold in the updated attacker model in which
// the attacker cannot guess Principal ids? why / why not?>
// No, the attacker can delete a message which is send_mode_on message and 
// repeat the message in the future period which is not send_mode_on
// that is  
// send_mode_on -> network
// ||
// \/
// attacker delete message
// ||
// \/
// ...
// ||
// \/
// other non send_mode_on -> network
// ||
// \/
// attacker repeat the previous message of send_mode_on ->network
// ||
// \/
// network -> receive_mode_on



// what additional restrictions need to be added to the attacker model?
// any message modified by the attacker will not contain the authorised_cards
//
//
// Attacks still permitted by the updated attacker model:
// Attack 3: repeat all previous messages
// Attack of repeating some previous messages may not be detected,
// especially those mode_on message which are deleted by attacker,
// or repeating those change setting message after a new change setting message
// has sent to the network and been received.
//
// Attack 4: modify the joules if the message is send joules message
// ICD has no aware of the original joules which the authorised_cards set
// thus, any attack of modifying jourles can not be detected and avoid.


// Relationship to our HAZOP study:
//
// (a)Which of these attacks are covered by hazards that you identified?
// 1.delete the message network the network
// This is covered in the previously assignment
// ID= 2.2, 5.2 6.2 ...
// we've suggest that to solve this kind of attacks,
// any request sent to the ICD should pair with response and
// import repeating machanism of sending message
//
// 2.interfere the network by sending an unauthorized message
// This is also coverd.
// ID = 1.2
// We've suggest to import machanism of authorisation and 
// authentication to ensure that the message is securied
//
// 3.repeat all previous messages
// The attack is NOT directly covered. But the solution of the attack
// can be similar to the one with
// ID = 2.5
// which is mark every sending message with count
// so that any previous message repeating will be ignored 
// since the current message count is greater
// 
// 4.modify the joules if the message is send joules message
// The attack is totally NOT covered.
//
//
// (b) Any new hazards suggested by these attacks, 
// including the design item that each
// applies to and an appropriate HAZOP guideword for each.
//
//
// Design item 1:
// In the off mode, when an authorised Cardiologist sends a
// change setting request, the ICD system should reset 
// the value of upper bound for tachycardia or the number
// of joules delivered and return the corresponding 
// ChangeSettingResponse.  
//
// Guide Word - PART OF
// Deviation: The change setting request is received but
// the joules set is not the original one
// Possible Cause: the message is modified by the attacker
//
// Guide Word - LATE
// Deviation: The ICD receives the changeSetting message after a period
// of time
// Possible Cause: The attacker delay the message by
// delete the message and repeat it after a period of time
//
//
// Design item 2:
// 2. When an authorised Cardiologist or Clinical Assistant switch on/off,
// ICD software must be set as on/off mode.
//
//
// Guide Word - LATE
// Deviation: The ICD receives the ModeOn/Off message after a period
// of time
// Possible Cause: The attacker delay the message by
// delete the message and repeat it after a period of time
//
//


