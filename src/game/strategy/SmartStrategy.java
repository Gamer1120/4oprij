package game.strategy;

import game.Board;
import game.Disc;

import java.util.ArrayList;
import java.util.Random;

/**
 * SmartStrategy for the Connect4 according to the protocol of the TI-2 group.<br>
 * <br>
 * Programming Project Connect4 Module 2 Softwaresystems 2014-2015 <br>
 * 
 * @author Michael Koopman s1401335 and Sven Konings s1534130
 */
public class SmartStrategy implements Strategy {
	/**
	 * The name this strategy has.
	 */
	public final static String NAME = "Smart";

	/**
	 * Returns the name this Strategy has.
	 */
	/*@ pure */@Override
	public String getName() {
		return NAME;
	}

	/**
	 * Determines a somewhat smart move on a given Board with a given Disc.
	 * First it checks, whether it can win instantly. Then it checks, if it
	 * makes a move, if the opponent can win.
	 * 
	 * @param b
	 *            The Board to make the move on.
	 * @param d
	 *            The Disc to make the move for.
	 */
	//@ requires b != null;
	@Override
	public int determineMove(Board b, Disc d) {
		ArrayList<Integer> empty = new ArrayList<Integer>();
		//@ loop_invariant 0 <= i & i <= b.getColumns();
		for (int i = 0; i < b.getColumns(); i++) {
			if (b.isEmptyField(i)) {
				empty.add(i);
			}
		}
		for (Integer i : empty) {
			Board board = b.deepCopy();
			board.insertDisc(i, d);
			if (board.gameOver()) {
				return i;
			}
		}
		for (Integer i : empty) {
			Board board = b.deepCopy();
			board.insertDisc(i, d.other());
			if (board.gameOver()) {
				return i;
			}
		}
		Random rng = new Random();
		return empty.get(rng.nextInt(empty.size()));
	}
}
