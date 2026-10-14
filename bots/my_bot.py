"""
My poker bot!

This is the only file you need to edit. Change decide() to change how your
bot plays.

Run it (the organiser will tell you the host and port):
    python3 my_bot.py --host 192.168.1.20 --port 8000

Practise against 3 copies of itself on your own computer (start the server
first: see "Practising on your own computer" in README.md):
    python3 my_bot.py --port 8000 --count 4 --quiet

On Windows, type `python` (or `py`) instead of `python3`.

Strategy: fuck it we ball but not in an all in typa way but more like on sum calculated type shi
  - Preflop: play a range of hands that widens the closer you sit to the
    button, and always raise rather than limp.
  - After the flop: estimate win chance by simulating random run-outs,
    bet big with strong hands, call when the pot odds are right, and
    sometimes bluff when opponents check.
  - Spots opponents who keep shoving ("maniacs") and calls them lighter.
  - Late in the 20 hands: tighten up when leading, gamble when behind.
"""
import itertools
import random
import threading
import time

from pokerbot import all_in, call, check, fold, raise_to, run
from pokerbot.cards import is_pair, is_suited, rank

BOT_NAME = "Pablo"

BIG_BLIND = 20


# ranges are top x of all starting hands, e.g. 0.12 = the best 12%.

EARLY_OPEN_RANGE = 0.12     # raise first in from early seats (88+, AJ+, KQ, suited connectors)
LATE_OPEN_RANGE = 0.25      # raise first in from the cutoff or button (adds 66+, AT+, KT+, QT+)
OPEN_SIZE = 3 * BIG_BLIND   # opening raise, plus one big blind per limper
CALL_OPEN_RANGE = 0.08      # call someone else's opening raise (99+, AQ+, KQs)
CALL_OPEN_MAX_STACK = 0.15  # ...as long as it costs at most 15% of our stack
BB_DEFEND_RANGE = 0.40      # in the big blind, call a small raise
BB_DEFEND_MAX_CALL = 3 * BIG_BLIND  # "small raise" = costs us at most this
HEADS_UP_OPEN_RANGE = 0.60  # only two players left: raise most hands from the button
HEADS_UP_DEFEND_RANGE = 0.50  # ...and defend the big blind wider too

VALUE_BET_EDGE = 1.3        # bet for value when our win chance is 1.3x a fair share
RAISE_EDGE = 1.8            # raise a bet when our win chance is 1.8x a fair share
VALUE_BET_SIZE = 0.65       # value bet as a fraction of the pot
BLUFF_FREQUENCY = 0.30      # how often to bluff when everyone checks to us
BLUFF_SIZE = 0.65           # bluff as a fraction of the pot
CBET_FREQUENCY = 0.0        # after raising preflop, bet the flop this often even if we missed
CBET_MIN_EDGE = 0.8         # ...but only with some chance to improve (overcards, draws)

CALL_MARGIN = 0.05          # extra win chance we want, on top of pot odds, to call
BETTOR_BLUFF_RATE = 0.25    # how often we think a bettor is bluffing
RERAISER_BLUFF_RATE = 0.10  # how often we think someone raising our bet is bluffing
ALL_IN_FRACTION = 0.7       # if a bet would use this much of our stack, go all in

MANIAC_BIG_RAISE = 15 * BIG_BLIND  # a raise this big counts as a "shove"
MANIAC_MIN_SHOVES = 2       # this many shoves and we treat them as a maniac
MANIAC_RAISE_RATE = 0.7    # ...or if they raise preflop this often
MANIAC_MIN_HANDS = 8      # ...over at least this many hands

LATE_HAND = 14              # from this hand on, adjust for the chip standings
LEADING_RANGE_FACTOR = 0.7  # when leading late, play 30% fewer hands
BEHIND_RANGE_FACTOR = 1.3   # when behind late, play 30% more hands
FINAL_HANDS = 2             # in the last 2 hands, if not leading...
FINAL_SHOVE_RANGE = 0.40    # ...go all in with the top 40% of hands

EQUITY_TIME = 1.0           # seconds to spend simulating (move timer is 5s)
EQUITY_MAX_SIMS = 4000      # stop early once we've run this many simulations


def decide(state):
    """Called every time it's your turn. Returns fold/check/call/raise_to/all_in."""
    update_opponent_stats(state)
    if state.street == "preflop":
        return decide_preflop(state)
    return decide_postflop(state)

# Preflop

def decide_preflop(state):
    cards = state.my_cards
    top = hand_percentile(cards)       # 0.0 = best hand (AA), 1.0 = worst (72o)
    leading = is_leading(state)
    late = state.hand_number >= LATE_HAND
    final = state.hand_number > state.hands_in_match - FINAL_HANDS

    # Last couple of hands and we're not winning: second place is worth
    # nothing, so gamble with anything reasonable.
    if final and not leading:
        if top <= FINAL_SHOVE_RANGE:
            return all_in()
        return check() if state.can_check else fold()

    # Late in the match, play fewer hands if leading and more if behind.
    factor = 1.0
    if late:
        factor = LEADING_RANGE_FACTOR if leading else BEHIND_RANGE_FACTOR

    raises = [m for m in state.history if m.street == "preflop" and m.action == "raise"]
    limpers = sum(1 for m in state.history if m.street == "preflop" and m.action == "call")

    heads_up = len(live_seats(state)) == 2

    # Nobody has raised yet: raise with a good hand, otherwise check or fold.
    # In the small blind with no limpers, only the big blind is left to act,
    # so it plays like a late seat.
    if not raises:
        if heads_up:
            open_range = HEADS_UP_OPEN_RANGE
        elif is_late_position(state) or (is_small_blind(state) and not limpers):
            open_range = LATE_OPEN_RANGE
        else:
            open_range = EARLY_OPEN_RANGE
        if top <= open_range * factor:
            return bet_to(state, OPEN_SIZE + limpers * BIG_BLIND)
        return check() if state.can_check else fold()

    raiser = raises[-1].name
    current_bet = state.my_bet + state.to_call

    # A maniac is raising: their hand is close to random, so get it all in
    # with any hand that's a clear favourite against a random one.
    if is_maniac(raiser) and beats_maniac(cards):
        return all_in()

    # Facing a re-raise (or more): only the very best hands continue.
    if len(raises) >= 2:
        return all_in() if is_premium(cards) else fold()

    # Facing a single raise.
    if is_premium(cards):
        return bet_to(state, 3 * current_bet)
    defend_range = HEADS_UP_DEFEND_RANGE if heads_up else BB_DEFEND_RANGE
    if is_big_blind(state) and state.to_call <= BB_DEFEND_MAX_CALL and top <= defend_range * factor:
        return call()
    if top <= CALL_OPEN_RANGE * factor and state.to_call <= CALL_OPEN_MAX_STACK * state.my_stack:
        return call()
    return fold()


def is_premium(cards):
    """QQ, KK, AA or AK."""
    high, low = sorted((rank(c) for c in cards), reverse=True)
    return (is_pair(cards) and high >= 12) or (high == 14 and low == 13)


def beats_maniac(cards):
    """Hands that are a clear favourite against a random hand: 77+, AT+, KQ."""
    high, low = sorted((rank(c) for c in cards), reverse=True)
    if is_pair(cards):
        return high >= 7
    return (high == 14 and low >= 10) or (high == 13 and low == 12)


def chen_score(cards):
    """
    The Chen formula: a classic quick way to score two starting cards.
    Higher is better (AA = 20, 72 offsuit = -1).
    """
    high, low = sorted((rank(c) for c in cards), reverse=True)
    points = {14: 10, 13: 8, 12: 7, 11: 6}.get(high, high / 2)
    if high == low:
        return max(points * 2, 5)
    if is_suited(cards):
        points += 2
    gap = high - low - 1
    points -= {0: 0, 1: 1, 2: 2, 3: 4}.get(gap, 5)
    if gap <= 1 and high < 12:
        points += 1                  # small connected cards can make straights
    return points


def _build_percentiles():
    """
    For each Chen score, where it ranks among all 1326 starting hands. Many
    hands share a score, so each score gets the middle of its group's ranks.
    """
    deck = [r + s for r in "23456789TJQKA" for s in "cdhs"]
    scores = sorted((chen_score(list(pair)) for pair in itertools.combinations(deck, 2)),
                    reverse=True)
    first, last = {}, {}
    for i, score in enumerate(scores):
        first.setdefault(score, i)
        last[score] = i + 1
    return {score: (first[score] + last[score]) / 2 / len(scores) for score in first}


_PERCENTILES = _build_percentiles()


def hand_percentile(cards):
    """Where these cards rank: 0.03 means "in the top 3% of starting hands"."""
    return _PERCENTILES[chen_score(cards)]



# post-flop / pre-turn

def decide_postflop(state):
    opponents = state.opponents_in_hand
    behind_late = state.hand_number >= LATE_HAND and not is_leading(state)
    bettor = last_bettor(state)

    
    # Maniacs bet anything, so their cards stay random.
    gain, honesty = 0, 0.0
    if not state.can_check and bettor and not is_maniac(bettor):
        we_bet = any(m.seat == state.my_seat and m.street == state.street and m.action == "raise"
                     for m in state.history)
        gain, honesty = (2, 1 - RERAISER_BLUFF_RATE) if we_bet else (1, 1 - BETTOR_BLUFF_RATE)

    win = equity(state.my_cards, state.board, len(opponents), gain, honesty)
    edge = win * (len(opponents) + 1)  # 1.0 = exactly our fair share of the pot

    # Nobody has bet: bet strong hands, sometimes bluff, otherwise check.
    if state.can_check:
        if edge >= VALUE_BET_EDGE:
            return bet_to(state, VALUE_BET_SIZE * state.pot)
        no_maniacs = not any(is_maniac(p.name) for p in opponents)

    
        preflop_raises = [m for m in state.history if m.street == "preflop" and m.action == "raise"]
        we_raised_last = preflop_raises and preflop_raises[-1].seat == state.my_seat
        if (state.street == "flop" and we_raised_last and no_maniacs and len(opponents) <= 2
                and edge >= CBET_MIN_EDGE and random.random() < CBET_FREQUENCY):
            return bet_to(state, BLUFF_SIZE * state.pot)

        checked_to_us = any(m.street == state.street and m.action == "check"
                            for m in state.history)
        if checked_to_us and no_maniacs and len(opponents) <= 2 and random.random() < BLUFF_FREQUENCY:
            return bet_to(state, BLUFF_SIZE * state.pot)
        return check()

    # Facing a bet: raise with a monster, call if the price is right.
    if edge >= RAISE_EDGE:
        return bet_to(state, 3 * (state.my_bet + state.to_call))
    margin = 0 if (behind_late or (bettor and is_maniac(bettor))) else CALL_MARGIN
    if win >= state.pot_odds + margin:
        return call()
    return fold()


def last_bettor(state):
    moves = [m for m in state.history if m.street == state.street and m.action == "raise"]
    return moves[-1].name if moves else None


# Cards as (rank, suit) pairs, so the simulation doesn't re-parse strings.
_DECK = [(r, s) for r in range(2, 15) for s in range(4)]
_SUITS = {"c": 0, "d": 1, "h": 2, "s": 3}


def _parse(card):
    return (rank(card), _SUITS[card[1]])


def equity(my_cards, board, num_opponents, bettor_gain=0, bettor_honesty=0.0):
    """
    Our chance of winning (0 to 1) against this many opponents, found by
    dealing out the rest of the hand thousands of times. Opponents hold
    random cards, except that with probability `bettor_honesty` one of them
    (the bettor) holds a hand at least `bettor_gain` hand types better than
    the board on its own (1 = a pair or better, 2 = two pair or better).
    Stops after EQUITY_TIME seconds so we never miss the move timer.
    """
    if num_opponents == 0:
        return 1.0
    mine = [_parse(c) for c in my_cards]
    table = [_parse(c) for c in board]
    known = set(mine + table)
    deck = [c for c in _DECK if c not in known]
    to_deal = 5 - len(table)
    deadline = time.time() + EQUITY_TIME

    board_level = best_hand(table)[0]

    wins = 0.0
    sims = 0
    while sims < EQUITY_MAX_SIMS and (sims % 50 or time.time() < deadline):
        cards = random.sample(deck, to_deal + 2 * num_opponents)
        # The first opponent dealt is the bettor. Unless this is one of their
        # bluffs, redeal until their cards beat the board by `bettor_gain` hand types.
        if bettor_gain and random.random() < bettor_honesty:
            for _ in range(30):
                if best_hand(cards[to_deal:to_deal + 2] + table)[0] >= board_level + bettor_gain:
                    break
                cards = random.sample(deck, to_deal + 2 * num_opponents)
        full_board = table + cards[:to_deal]
        my_best = best_hand(mine + full_board)
        their_best = max(best_hand(cards[to_deal + 2 * i:to_deal + 2 * i + 2] + full_board)
                         for i in range(num_opponents))
        if my_best > their_best:
            wins += 1
        elif my_best == their_best:
            wins += 0.5
        sims += 1
    return wins / sims


def _straight_high(ranks):
    """The top card of the best straight in these ranks, or 0 if there isn't one."""
    if 14 in ranks:
        ranks = ranks | {1}          # an Ace can also be low: A-2-3-4-5
    for high in range(14, 4, -1):
        if all(high - i in ranks for i in range(5)):
            return high
    return 0


def best_hand(cards):
    """
    Score the best 5-card hand from up to 7 (rank, suit) cards. Returns a
    tuple: bigger tuples are better hands, so two hands compare with > and ==.
    """
    counts = [0] * 15
    by_suit = [[], [], [], []]
    for r, s in cards:
        counts[r] += 1
        by_suit[s].append(r)

    flush = next((sorted(lst, reverse=True) for lst in by_suit if len(lst) >= 5), None)
    if flush:
        high = _straight_high(set(flush))
        if high:
            return (8, high)

    ranks = [r for r in range(14, 1, -1) if counts[r]]   # each rank once, best first
    quads = [r for r in ranks if counts[r] == 4]
    trips = [r for r in ranks if counts[r] == 3]
    pairs = [r for r in ranks if counts[r] == 2]

    def kickers(used, n):
        return tuple(r for r in ranks if r not in used)[:n]

    if quads:
        return (7, quads[0]) + kickers(quads[:1], 1)
    if trips and (len(trips) >= 2 or pairs):
        top_pair = max(trips[1:] + pairs)
        return (6, trips[0], top_pair)
    if flush:
        return (5,) + tuple(flush[:5])
    high = _straight_high(set(ranks))
    if high:
        return (4, high)
    if trips:
        return (3, trips[0]) + kickers(trips[:1], 2)
    if len(pairs) >= 2:
        return (2, pairs[0], pairs[1]) + kickers(pairs[:2], 1)
    if pairs:
        return (1, pairs[0]) + kickers(pairs[:1], 3)
    return (0,) + kickers([], 5)

# Table position and chip standings

def live_seats(state):
    """Seat numbers of everyone still in the match, in seat order."""
    seats = [p.seat for p in state.opponents if p.status != "out"] + [state.my_seat]
    return sorted(seats)


def is_late_position(state):
    """True on the button or the seat just before it (the cutoff), outside the blinds."""
    if is_big_blind(state) or is_small_blind(state):
        return False
    seats = live_seats(state)
    if state.button not in seats:
        return False
    seats_to_button = (seats.index(state.button) - seats.index(state.my_seat)) % len(seats)
    return seats_to_button <= 1


def is_big_blind(state):
    return any(m.seat == state.my_seat and m.action == "big_blind" for m in state.history)


def is_small_blind(state):
    return any(m.seat == state.my_seat and m.action == "small_blind" for m in state.history)


def is_leading(state):
    """True if we have more chips than every opponent (counting chips bet this round)."""
    mine = state.my_stack + state.my_bet
    best_other = max((p.stack + p.bet for p in state.opponents if p.status != "out"), default=0)
    return mine > best_other



# Helpers

def bet_to(state, total):
    """Raise to `total`, or go all in if that would use most of our stack anyway."""
    if not state.can_raise:
        return call() if state.to_call else check()
    total = int(total)
    if total >= ALL_IN_FRACTION * state.max_raise:
        return all_in()
    return raise_to(max(state.min_raise, total))



# Maniac spotting

_memory = threading.local()


def _stats():
    if not hasattr(_memory, "players"):
        _memory.players = {}    # name -> {"hands": set, "raised": set, "shoves": set}
        _memory.match = 0
        _memory.hand = None
        _memory.seen = 0        # how many history moves we've already counted
    return _memory


def update_opponent_stats(state):
    mem = _stats()
    if mem.hand is not None and state.hand_number < mem.hand:
        mem.match += 1          # hand numbers went back down: a new match started
    if state.hand_number != mem.hand:
        mem.hand = state.hand_number
        mem.seen = 0
    hand_id = (mem.match, state.hand_number)

    for move in state.history[mem.seen:]:
        if move.seat == state.my_seat or move.action in ("small_blind", "big_blind"):
            continue
        player = mem.players.setdefault(move.name, {"hands": set(), "raised": set(), "shoves": set()})
        player["hands"].add(hand_id)
        if move.action == "raise" and move.street == "preflop":
            player["raised"].add(hand_id)
        if move.action == "raise" and move.amount >= MANIAC_BIG_RAISE:
            player["shoves"].add(hand_id)
    mem.seen = len(state.history)


def is_maniac(name):
    player = _stats().players.get(name)
    if not player:
        return False
    if len(player["shoves"]) >= MANIAC_MIN_SHOVES:
        return True
    hands = len(player["hands"])
    return hands >= MANIAC_MIN_HANDS and len(player["raised"]) / hands >= MANIAC_RAISE_RATE


# ----------------------------------------------------------------------
# You don't need to change anything below this line.
if __name__ == "__main__":
    run(decide, name=BOT_NAME)
