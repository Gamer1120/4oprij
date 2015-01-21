package game;
import java.util.Observable;

/**
 * Abstract class for keeping a player in the Connect4 game.<br>
 * <br>
 * Programming Project Connect4 Module 2 Softwaresystems 2014-2015 <br>
 * 
 * @author Michael Koopman s1401335 and Sven Konings s1534130
 */
public abstract class Player extends Observable {

	// Instance variables:
	private String name;
	private Disc disc;

	// Constructors:
	/*@
		requires theName != null;
		requires theDisc == Disc.YELLOW || theDisc == Disc.RED;
		ensures this.getName() == theName; ensures this.getDisc() == theDisc;
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
		super.setChanged();
		super.notifyObservers(name + " made a move");
	}

}
