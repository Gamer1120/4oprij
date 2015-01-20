package clientserver;

import game.Board;

import java.util.Arrays;
import java.util.HashSet;

public class Game {
	//PROTOCOL
	/** The Constant WIN. */
	public static final String WIN = "WIN";

	/** The Constant DRAW. */
	public static final String DRAW = "DRAW";

	/** The Constant DISCONECT. */
	public static final String DISCONNECT = "DISCONNECT";
	//END PROTOCOL

	private ClientHandler[] team0;
	private ClientHandler[] team1;
	private int currPlayer0;
	private int currPlayer1;
	private int currTeam;
	private HashSet<ClientHandler> clients;
	private int[] boardSize;
	private Board board;

	//TODO: discuss teams or more discs
	public Game(ClientHandler[] players, int boardX, int boardY) {
		this.clients = new HashSet<ClientHandler>();
		clients.addAll(Arrays.asList(players));
		this.boardSize = new int[] { boardX, boardY };
		int teamSize = (players.length) / 2;
		this.team0 = Arrays.copyOfRange(players, 0, teamSize - 1);
		this.team1 = Arrays.copyOfRange(players, teamSize - 1,
				players.length - 1);
	}

	public void add(ClientHandler client) {
		clients.add(client);
	}

	public void startGame() {
		board = new Board(boardSize[0], boardSize[1]);
		currTeam = 0;
	}

	@SuppressWarnings("unused")
	private void requestMove() {
		if (currTeam == 0) {
			team0[currPlayer0].sendMessage("");
			currPlayer0 = (currPlayer0 + 1) % team0.length - 1;
			currTeam = 1;
		} else {
			team1[currPlayer1].sendMessage("");
			currPlayer1 = (currPlayer1 + 1) % team1.length - 1;
			currTeam = 0;
		}
	}

	public boolean isValidMove(int col) {
		return board.isField(col) && board.isEmptyField(col);
	}

	public void doMove(int col) {
		for (ClientHandler ch : clients) {
			ch.sendMessage("MOVE_OK");
		}
	}

	public String[] getPlayers() {
		String[] players = new String[team0.length + team1.length - 2];
		for (int i = 0; i < team0.length + team1.length - 2; i++) {
			if (i < team0.length - 1) {
				players[i] = team0[i].getClientName();
			} else {
				players[i] = team1[i - team0.length].getClientName();
			}
		}
		return players;
	}
}
