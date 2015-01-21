package game;

import clientserver.ClientView;

/**
 * Class for maintaining a human player in Tic Tac Toe.
 * 
 * @author Sven Konings en Michael Koopman
 */
public class HumanPlayer extends Player {
	/**
	 * The View used by the Client
	 */
	private ClientView view;

	// Constructors:
	/*@
		requires disc == Disc.YELLOW || disc == Disc.RED;
		ensures this.getDisc() == disc;
	 */
	/**
	 * Creates a new HumanPlayer object with a given Disc and ClientView.
	 */
	public HumanPlayer(Disc disc, ClientView viewArg) {
		super("HumanPlayer", disc);
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
