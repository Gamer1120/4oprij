package game;

import clientserver.ClientView;

/**
 * Class for maintaining a human player in Tic Tac Toe.
 * 
 * @author Sven Konings en Michael Koopman
 * @version $Revision: 1.0 $
 */
public class HumanPlayer extends Player {
	/**
	 * View of the game
	 */
	private ClientView view;

	// Constructors:
	/*@
		requires name != null;
		requires mark == Mark.XX || mark == Mark.OO;
		ensures this.getName() == name;
		ensures this.getMark() == mark;
	 */
	/**
	 * Creates a new human player object.
	 */
	public HumanPlayer(String name, Disc disc, ClientView viewArg) {
		super(name, disc);
		view = viewArg;
	}

	// Commands:

	/*@
		requires board != null;
		ensures board.isField(\result) && board.isEmptyField(\result);
	 */
	/**
	 * Asks the user to input the field where to place the next mark. This is
	 * done using the view.
	 * 
	 * @param board
	 *            the game board
	 * @return the player's chosen field
	 */
	public int determineMove(Board board) {
		return view.makeMove();
	}
}
