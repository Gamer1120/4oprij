import java.util.Observable;

/**
 * Abstract class for keeping a player in the Connect4 game.
 * 
 * @author Sven Konings en Michael Koopman
 * @version $Revision: 1.0 $
 */
public abstract class Player extends Observable {

	// Instance variables:
	private String name;
	private Disc disc;

	// Constructors:
	/*@
		requires theName != null;
		requires thedisc == thedisc.XX || thedisc == thedisc.OO;
		ensures this.getName() == theName; ensures this.getdisc() == thedisc;
	 */
	/**
	 * Creates a new Player object.
	 */
	public Player(String theName, Disc theDisc) {
		name = theName;
		disc = theDisc;
	}

	// Queries:
	/**
	 * Returns the name of the player.
	 */
	/*@pure*/public String getName() {
		return name;
	}

	/**
	 * Returns the disc of the player.
	 */
	/*@pure*/public Disc getDisc() {
		return disc;
	}

	/*@
		requires board != null & !board.isFull();
		ensures board.isField(\result) & board.isEmptyField(\result);
	 */
	/**
	 * Determines the field for the next move.
	 * 
	 * @param board
	 *            the current game board
	 * @return the player's choice
	 */
	public abstract int determineMove(Board board);

	// Commands:
	/*@requires board != null & !board.isFull();*/
	/**
	 * Makes a move on the board.
	 * 
	 * @param bord
	 *            the current board
	 */
	public void makeMove(Board board) {
		int keuze = determineMove(board);
		board.insertDisc(keuze, getDisc());
		//TODO: Notify move gedaan
	}

}
