/**
 * Represents a disc in the connect4 game. There three possible values:
 * Disc.YELLOW, Disc.RED and Disc.EMPTY.
 * 
 * @author Sven Konings en Michael Koopman
 * @version $Revision: 1.0 $
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
