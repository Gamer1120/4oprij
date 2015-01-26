package game;

/**
 * Strategy interface for the Connect4 according to the protocol of the TI-2
 * group.<br>
 * <br>
 * Programming Project Connect4 Module 2 Softwaresystems 2014-2015 <br>
 * 
 * @author Michael Koopman s1401335 and Sven Konings s1534130
 */
public interface Strategy {
	/**
	 * Returns the name this Strategy has.
	 * 
	 * @return The name this strategy has.
	 */
	/*@ pure */public String getName();

	/**
	 * Determines a move for the ComputerPlayer this Strategy is assigned to.
	 * 
	 * @param b
	 *            The Board to make a move on.
	 * @param d
	 *            The Disc to make a move for.
	 * @return The move determined by the strategy.
	 */
	/*@	requires b != null;
	 	requires d == Disc.YELLOW || Disc.RED;
	 */
	public int determineMove(Board b, Disc d);
}
