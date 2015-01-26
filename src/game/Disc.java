package game;

/**
 * Represents a disc in the Connect4 game. There are three possible values:
 * Disc.YELLOW, Disc.RED and Disc.EMPTY.<br>
 * <br>
 * Programming Project Connect4 Module 2 Softwaresystems 2014-2015 <br>
 * 
 * @author Sven Konings en Michael Koopman
 */
public enum Disc {

	EMPTY, YELLOW, RED;

	/*@
		ensures this == Disc.YELLOW ==> \result == Disc.RED;
		ensures this == Disc.RED ==> \result == Disc.YELLOW;
		ensures this == Disc.EMPTY ==> \result == Disc.EMPTY;
	 */
	/**
	 * Returns the other disc.
	 * 
	 * @return the other disc is this disc is not EMPTY
	 */
	public Disc other() {
		if (this == YELLOW) {
			return RED;
		} else if (this == RED) {
			return YELLOW;
		} else {
			return EMPTY;
		}
	}

	/**
	 * Returns a better String representation of the Disc, for the toString in
	 * Board.
	 */
	@Override
	public String toString() {
		if (this == RED) {
			return "R";
		} else if (this == YELLOW) {
			return "Y";
		} else {
			return " ";
		}
	}
}
