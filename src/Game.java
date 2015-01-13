/**
 * Class for maintaining the Tic Tac Toe game.
 * 
 * @author Sven Konings en Michael Koopman
 * @version $Revision: 1.0 $
 */
public class Game {
	// Instance variables:
	public static final int NUMBER_PLAYERS = 2;

	/*@private invariant board != null;*/
	/**
	 * The board.
	 */
	private Board board;

	/*@
		private invariant players.length == NUMBER_PLAYERS;
		private invariant (\forall int i; 0 <= i && i < NUMBER_PLAYERS; players[i] != null);
	 */
	/**
	 * The 2 players of the game.
	 */
	private Player[] players;

	/*@private invariant 0 <= current && current < NUMBER_PLAYERS;*/
	/**
	 * Index of the current player.
	 */
	private int current;

	/**
	 * View of the game
	 */
	private GameView view;

	// Constructors:
	/*@
		requires s0 != null;
		requires s1 != null;
	 */
	/**
	 * Creates a new Game object.
	 * 
	 * @param s0
	 *            the first player
	 * @param s1
	 *            the second player
	 */
	public Game(Player s0, Player s1, GameView v) {
		board = new Board();
		players = new Player[NUMBER_PLAYERS];
		players[0] = s0;
		players[1] = s1;
		current = 0;
		view = v;
		players[0].addObserver(view);
		players[1].addObserver(view);
	}

	// Commands:
	/**
	 * Starts the Tic Tac Toe game. Asks after each ended game if the user want
	 * to continue. Continues until the user does not want to play anymore.
	 */
	public void start() {
		view.start();
	}

	/**
	 * Resets the game. The board is emptied and player[0] becomes the current
	 * player.
	 */
	public void reset() {
		current = 0;
		board.reset();
	}

	/**
	 * Plays the Tic Tac Toe game. First the (still empty) board is shown. Then
	 * the game is played until it is over. Players can make a move one after
	 * the other. After each move, the changed game situation is printed.
	 */
	public void play() {
		view.update(board);
		current = 0;
		while (!board.gameOver()) {
			players[current].makeMove(board);
			view.update(board);
			current = (current + 1) % NUMBER_PLAYERS;
		}
		printResult();
	}

	/*@requires this.board.gameOver();*/
	/**
	 * Prints the result of the last game.
	 */
	public void printResult() {
		if (board.hasWinner()) {
			Player winner = board.isWinner(players[0].getDisc()) ? players[0]
					: players[1];
			view.printResult(winner);
		} else {
			view.printResult(null);
		}
	}
}
