package strategy;

import game.Board;
import game.Disc;

import java.util.Observable;

/**
 * Class for maintaining a ComputerPlayer in Connect4.<br>
 * <br>
 * Programming Project Connect4 Module 2 Softwaresystems 2014-2015 <br>
 * 
 * @author Michael Koopman s1401335 and Sven Konings s1534130
 */
public class ComputerPlayer extends Observable {

	/**
	 * The Strategy used by this ComputerPlayer
	 */
	private Strategy s;
	/**
	 * The Disc this ComputerPlayer should use
	 */
	private Disc d;

	/*@ private invariant s != null;
		private invariant d == Disc.YELLOW || d == Disc.RED;
	 */

	/**
	 * Creates a new ComputerPlayer object with a given Disc and a
	 * SmartStrategy.
	 * 
	 * @param disc
	 *            The Disc this ComputerPlayer should have.
	 */
	/*@	requires disc == Disc.YELLOW || disc == Disc.RED;
	 	ensures getDisc() == disc;
	 	ensures getStrategy() != null;
	 */
	public ComputerPlayer(Disc disc) {
		this(disc, new SmartStrategy());
	}

	/**
	 * Creates a new ComputerPlayer object with a given Disc and Strategy.
	 * 
	 * @param disc
	 *            The Disc this ComputerPlayer should have.
	 * @param strategy
	 *            The Strategy this ComputerPlayer should use.
	 */
	/*@	requires disc == Disc.YELLOW || disc == Disc.RED;
	  	requires strategy != null;
	  	ensures getStrategy() == strategy;
	  	ensures getDisc() == disc;
	 */
	public ComputerPlayer(Disc disc, Strategy strategy) {
		s = strategy;
		d = disc;
	}

	/**
	 * Returns the disc of this player.
	 * 
	 * @return The Disc of this player.
	 */
	/*@pure*/public Disc getDisc() {
		return d;
	}

	/**
	 * Returns the Strategy the ComputerPlayer uses.
	 * 
	 * @return The Strategy the ComputerPlayer uses.
	 */
	/*@ pure */public Strategy getStrategy() {
		return s;
	}

	/**
	 * Sets the Strategy for this ComputerPlayer
	 * 
	 * @param strategy
	 *            The Strategy this ComputerPlayer should have.
	 */
	//@ ensures getStrategy() == strategy;
	public void setStrategy(Strategy strategy) {
		s = strategy;
	}

	/**
	 * Determines a move for this ComputerPlayer using it's Strategy.
	 * 
	 * @param b
	 *            The Board the move should be made on.
	 * @return A move determined by the Strategy this ComputerPlayer has.
	 */
	//@ requires b != null;
	//@ ensures b.isField(\result) && b.isEmptyField(\result);
	public int determineMove(Board b) {
		int move = s.determineMove(b, d);
		super.setChanged();
		super.notifyObservers("Determined a move");
		return move;
	}
}
