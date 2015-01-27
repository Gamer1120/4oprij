package game.strategy;

import game.Board;
import game.Disc;

import java.util.ArrayList;
import java.util.Random;

/**
 * NaiveStrategy for the Connect4 according to the protocol of the TI-2 group.<br>
 * <br>
 * Programming Project Connect4 Module 2 Softwaresystems 2014-2015 <br>
 * 
 * @author Michael Koopman s1401335 and Sven Konings s1534130
 */
public class NaiveStrategy implements Strategy {
	/**
	 * The name this game.strategy has.
	 */
	public final static String NAME = "Naive";

	/**
	 * Returns the name this Strategy has.
	 */
	/*@ pure */@Override
	public String getName() {
		return NAME;
	}

	/**
	 * Determines a random move on a given Board with a given Disc.
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
		//@ loop_invariant 0 <= col & col <= b.getColumns();
		for (int col = 0; col < b.getColumns(); col++) {
			if (b.isEmptyField(col)) {
				empty.add(col);
			}
		}
		Random rng = new Random();
		return empty.get(rng.nextInt(empty.size()));
	}
}
