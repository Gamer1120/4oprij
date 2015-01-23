package clientserver;

import game.Board;
import game.ComputerPlayer;
import game.Disc;
import game.NaiveStrategy;
import game.SmartStrategy;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.InetAddress;
import java.net.Socket;
import java.util.HashMap;
import java.util.Map;

/**
 * Client program for the Connect4 according to the protocol of the TI-2 group.<br>
 * <br>
 * Programming Project Connect4 Module 2 Softwaresystems 2014-2015 <br>
 * 
 * @author Michael Koopman s1401335 and Sven Konings s1534130
 */
public class Client extends Thread {
	// The protocol, as discussed in our TI-2 group. For further explanation,
	// you can look at the protocol documentation.
	public static final String CONNECT = "CONNECT";
	public static final String QUIT = "QUIT";
	public static final String INVITE = "INVITE";
	public static final String ACCEPT_INVITE = "ACCEPT";
	public static final String DECLINE_INVITE = "DECLINE";
	public static final String MOVE = "MOVE";
	public static final String CHAT = "CHAT";
	public static final String REQUEST_BOARD = "REQUEST";
	public static final String REQUEST_LOBBY = "LOBBY";
	public static final String REQUEST_LEADERBOARD = "LEADERBOARD";
	public static final String ERROR = "ERROR";
	public static final String PING = "PING";
	// END OF PROTOCOL
	private static final String CLIENT_FEATURES = Features.CHAT + " "
			+ Features.CUSTOM_BOARD_SIZE + " " + Features.LEADERBOARD;
	public String firstPlayer;
	public String secondPlayer;

	/**
	 * The name of this Client.
	 */
	private String clientName;

	/**
	 * The User Interface of this Client.
	 */
	private ClientTUI mui;

	/**
	 * The Socket
	 */
	private Socket sock;
	/**
	 * The BufferedReader that will be used to communicate over the Socket.
	 */
	private BufferedReader in;
	/**
	 * The BufferedWriter that will be used to communicate over the Socket.
	 */
	private BufferedWriter out;
	/**
	 * While this boolean is true, it makes sure that commands are continuously
	 * read from the BufferedReader.
	 */
	private boolean loop;

	/**
	 * The Board this Client uses for determining their move.
	 */
	private Board board;
	/**
	 * An integer to determine which Player's turn it is.
	 */
	private String currPlayer;
	/**
	 * A boolean to determine whether this Client is connected.
	 */
	private Boolean isConnected;
	/**
	 * The Player this Client is.
	 */
	private ComputerPlayer computerPlayer;
	/**
	 * If the Client requests the Board from the server, it's saved here that it
	 * has already been requested, so it's not requested for a second time.
	 */
	private boolean boardRequested;
	/**
	 * A boolean to determine whether the server has requested a move.
	 */
	private boolean moveRequested;
	/**
	 * A Map of invites this Client is invited by. This map gets emptied every
	 * time a Game starts.
	 */
	private Map<String, Integer[]> invitedBy;
	/**
	 * A Map of invited this Client sent. This map gets emptied every time a
	 * Game starts.
	 */
	private Map<String, Integer[]> invited;

	/*@	private invariant sock != null;
	 	private invariant mui != null;
	 	private invariant in != null;
	 	private invariant out != null;
	  	private invariant invited != null;
	  	private invariant invitedBy != null;
	  	private invariant localPlayer != null;
	 */

	/**
	 * Constructs a Client object and tries to make a Socket connection
	 * 
	 * @param host
	 *            The IP-adress of this Client
	 * @param port
	 *            The port of this Client
	 * @param muiArg
	 *            The MessageUI for this Client
	 * @param computerPlayer
	 *            The Player Object to use for this Client
	 * @throws IOException
	 */
	/*@ requires host != null;
	 	requires port >= 1 & port <= 65535;
	 	requires muiArg != null;
	 	requires localPlayer != null;
	 */
	public Client(InetAddress host, int port, ClientTUI muiArg)
			throws IOException {
		this.mui = muiArg;
		this.sock = new Socket(host, port);
		this.in = new BufferedReader(new InputStreamReader(
				sock.getInputStream()));
		this.out = new BufferedWriter(new OutputStreamWriter(
				sock.getOutputStream()));
		this.isConnected = null;
		this.invited = new HashMap<String, Integer[]>();
		this.invitedBy = new HashMap<String, Integer[]>();
		this.loop = true;
		this.board = null;
		this.boardRequested = false;
		this.moveRequested = false;
		this.computerPlayer = null;
	}

	/**
	 * This method reads the messages in the InputStream. Then, it decides which
	 * command was sent, and executes this command by calling the method created
	 * for it.
	 */
	public void run() {
		while (loop) {
			String line = null;
			String[] serverMessage = null;
			try {
				line = in.readLine();
				serverMessage = line.split("\\s+");
			} catch (IOException | NullPointerException e) {
				shutdown();
				break;
			}
			mui.addMessage("[SERVER]" + line);
			switch (serverMessage[0]) {
			case Server.ACCEPT_CONNECT:
				isConnected = true;
				connect(serverMessage);
				break;
			case Server.LOBBY:
				lobby(serverMessage);
				break;
			case Server.INVITE:
				invite(serverMessage);
				break;
			case Server.DECLINE_INVITE:
				declineInvite(serverMessage);
				break;
			case Server.GAME_START:
				gameStart(serverMessage);
				break;
			case Server.GAME_END:
				gameEnd(serverMessage);
				break;
			case Server.REQUEST_MOVE:
				requestMove(serverMessage);
				break;
			case Server.MOVE_OK:
				moveOK(serverMessage);
				break;
			case Server.ERROR:
				//TODO: Zet dit netjes neer.
				mui.addMessage("[ERROR]" + line.split(" ", 2)[1]);
				if (!isConnected) {
					isConnected = null;
				}
				break;
			case Server.BOARD:
				board = toBoard(line);
				notifyAll();
				break;
			case Server.CHAT:
				mui.addMessage("[CHAT]" + line.split(" ", 2)[1]);
				break;
			case Server.LEADERBOARD:
				showLeaderBoard(serverMessage);
				break;
			case Server.PONG:
				mui.addMessage("[PING]Pong!");
				break;
			default:
				sendMessage(ERROR + " " + serverMessage[0]
						+ " Unknown command.");
				break;
			}
		}
	}

	/**
	 * This method accepts the Server.CONNECT packet sent by the Server. When
	 * this method is called, it prints that a connection has been established
	 * with the Server, as well as the IP adress and port of the Server. After
	 * this, it lists the features the Server has.
	 * 
	 * @param serverMessage
	 *            The full message the server sent.
	 */
	//@	requires serverMessage[0].equals(Server.ACCEPT_CONNECT);
	private void connect(String[] serverMessage) {
		mui.addMessage("[CONNECT]Successfully established connection to server: "
				// IP of the server
				+ sock.getRemoteSocketAddress().toString());
		mui.addMessage("[FEATURES]The features of this server are:"
				+ arrayToLine(serverMessage));
	}

	/**
	 * This method accepts the Server.LOBBY packet sent by the Server. When this
	 * method is called, it shows the Client the other Clients that are
	 * currently in the lobby.
	 * 
	 * @param serverMessage
	 *            The full message the server sent.
	 */
	//@ requires serverMessage[0].equals(Server.LOBBY);
	private void lobby(String[] serverMessage) {
		mui.addMessage("[LOBBY]The people that are currently in the lobby are:"
				+ arrayToLine(serverMessage));
	}

	/**
	 * This method accepts the Server.INVITE packet sent by the Server. When
	 * this method is called, it adds the inviter (and to an inviterlist, and
	 * potentially, the custom board size. If the player isn't ingame, it will
	 * also show the Client that they have been invited by that Client.
	 * 
	 * @param serverMessage
	 *            The full message the server sent.
	 */
	//@ requires serverMessage[0].equals(Server.INVITE);
	private void invite(String[] serverMessage) {
		String opponentName = serverMessage[1];
		if (serverMessage.length == 2) {
			addServerInvite(opponentName);
			if (!isIngame()) {
				mui.addMessage("[INVITE]"
						+ opponentName
						+ " has invited you to a game of Connect4 (default boardsize)!");
				mui.addMessage("Use \"ACCEPT " + opponentName
						+ "\" to accept this invite or \"DECLINE "
						+ opponentName + "\" to decline it.");
			}
		} else if (serverMessage.length >= 4) {
			try {
				int boardX = Integer.parseInt(serverMessage[2]);
				int boardY = Integer.parseInt(serverMessage[3]);
				addServerInvite(opponentName, boardX, boardY);
				if (!isIngame()) {
					mui.addMessage("[INVITE]"
							+ opponentName
							+ " has invited you to a game of Connect4 with a custom Board size of "
							+ boardX + " x " + boardY + "!");
					mui.addMessage("Use \"ACCEPT " + opponentName
							+ "\" to accept this invite or \"DECLINE "
							+ opponentName + "\" to decline it.");
				}
			} catch (NumberFormatException e) {
				mui.addMessage("[ERROR]The server just sent an invite with an invalid custom board size.");
				sendMessage(ERROR
						+ " "
						+ INVITE
						+ " Your server just sent me an invite with an invalid custom board size :(");
			}
		}
	}

	/**
	 * This method accepts the Server.DECLINE_INVITE packet. If the Server
	 * specified a person, the person will be removed from the list of people
	 * this Client has invited.
	 * 
	 * @param serverMessage
	 *            The full messsage the server sent.
	 */
	private void declineInvite(String[] serverMessage) {
		if (serverMessage.length > 1) {
			invited.remove(serverMessage[1]);
			mui.addMessage("[INVITE]The invite you sent to " + serverMessage[1]
					+ " got declined.");
		} else {
			mui.addMessage("[INVITE]The server just tried to decline one of your invites, but it didn't send who declined yours.");
			sendMessage(ERROR + " " + serverMessage[0]
					+ " Your server didn't send me who declined the invite.");
		}
	}

	/**
	 * This method accepts the Server.GAME_START packet sent by the Server. When
	 * this method is called, it will show the Client that a the game is
	 * started. The Client is set to being in-game, and a new Board is created.
	 * The size of the Board is dependant on the size sent in the invite (the
	 * Boardsizes of the invites are saved in a HashMap).
	 * 
	 * @param serverMessage
	 *            The full message the server sent.
	 */
	/*@ requires serverMessage[0].equals(Server.GAME_START);
	 	ensures board != null;
	 	ensures this.isIngame;
	 	ensures currPlayer == null;
	 */
	private void gameStart(String[] serverMessage) {
		firstPlayer = serverMessage[1];
		secondPlayer = serverMessage[2];

		if (firstPlayer.equals(getClientName())) {
			mui.addMessage("[GAME]A game between you and " + secondPlayer
					+ " has started!");
			Integer[] boardSize = invitedBy.get(secondPlayer);

			board = new Board(boardSize[1], boardSize[0]);
		} else {
			mui.addMessage("[GAME]A game between you and " + firstPlayer
					+ " has started!");
			Integer[] boardSize = invited.get(firstPlayer);
			board = new Board(boardSize[1], boardSize[0]);
		}

		currPlayer = null; // Not set yet.
		// DEFINITION: currPlayer == 0 > Disc.YELLOW, currPlayer ==
		// 1 > Disc.RED
		mui.addMessage(board.toString());
		mui.addMessage("[GAME]You are YELLOW");
	}

	/**
	 * This method accepts the Server.GAME_END packet sent by the Server. When
	 * this method is called, it will set the Client to no longer being in-game.
	 * It will also show the client who won the game, or if the game was a draw.
	 * 
	 * @param serverMessage
	 *            The full message the server sent.
	 */
	/*@	requires serverMessage[0].equals(Server.GAME_END);
	 	ensures !this.isIngame;
	 */
	private void gameEnd(String[] serverMessage) {
		this.board = null;
		if (serverMessage.length > 2) {
			mui.addMessage("[GAME]The winner is: " + serverMessage[2]);
		} else if (serverMessage.length == 2) {
			if (serverMessage[1].equals(Game.DRAW)) {
				mui.addMessage("[GAME]The game was a draw!");
			} else {
				mui.addMessage("[GAME]The game has ended. Reason:"
						+ arrayToLine(serverMessage));
			}
		}
	}

	/**
	 * This method accepts the Server.MOVE packet sent by the Server. When this
	 * method is called, it will request a move from the Player. If the Player
	 * is a HumanPlayer, the GameView will be used to ask for a move. If the
	 * Player is a ComputerPlayer, the determineMove() method from the
	 * ComputerPlayer is used instead.
	 * 
	 * @param serverMessage
	 *            The full message the server sent.
	 */
	//@ requires serverMessage[0].equals(Server.REQUEST_MOVE);
	private void requestMove(String[] serverMessage) {
		if (currPlayer == null) {
			currPlayer = firstPlayer;
		}
		if (computerPlayer == null) {
			moveRequested = true;
			mui.addMessage("Please enter a move");
			;
		} else {
			int move = computerPlayer.determineMove(board);
			sendMessage(MOVE + " " + move);
		}
	}

	/**
	 * This method accepts the Server.MOVE_OK packet sent by the Server. When
	 * this method is called, it will update the Board by inserting the Disc for
	 * the Player that was given in the packet. If it can't insert the Disc, it
	 * will request the Board and try to insert the Disc once again.
	 * 
	 * @param serverMessage
	 *            The full message the server sent.
	 */
	//@ requires serverMessage[0].equals(Server.MOVE_OK);
	private synchronized void moveOK(String[] serverMessage) {
		if (currPlayer == null) {
			currPlayer = secondPlayer;
		}
		int move = -1;
		if (currPlayer.equals(firstPlayer)) {
			try {
				move = Integer.parseInt(serverMessage[2]);
			} catch (NumberFormatException e) {
				mui.addMessage("[ERROR]Server did not send a valid move. TERMINATING.");
				sendMessage(ERROR + " " + Server.MOVE_OK
						+ " You didn't send a valid move.");
				shutdown();
			}
			if (board.isField(move) && board.isEmptyField(move)) {
				board.insertDisc(move, Disc.YELLOW);
				currPlayer = secondPlayer;
			} else {
				if (!boardRequested) {
					requestBoard();
					boardRequested = true;
					try {
						wait();
						mui.addMessage("[BOARD]This is the board the server has: ");
						mui.addMessage(board.toString());
						moveOK(serverMessage);
					} catch (InterruptedException e) {
						mui.addMessage("[ERROR]Interrupted. TERMINATING.");
						sendMessage(ERROR + " " + Server.BOARD
								+ " My client got interrupted.");
						shutdown();
					}
				} else {
					mui.addMessage("[ERROR]Can't make the move on both the local board, and the board on the server. TERMINATING.");
					sendMessage(ERROR
							+ " "
							+ Server.BOARD
							+ " I can't make the specified move on the local board, and the Board you just sent me. TERMINATING.");
					shutdown();
				}
			}
		} else if (currPlayer.equals(secondPlayer)) {
			try {
				move = Integer.parseInt(serverMessage[2]);
			} catch (NumberFormatException e) {
				mui.addMessage("[ERROR]Server did not send a valid move. TERMINATING.");
				sendMessage(ERROR + " " + Server.MOVE_OK
						+ " You didn't send a valid move.");
				shutdown();
			}
			if (board.isField(move) && board.isEmptyField(move)) {
				board.insertDisc(move, Disc.RED);
				currPlayer = firstPlayer;
			} else {
				if (!boardRequested) {
					requestBoard();
					boardRequested = true;
					try {
						wait();
						moveOK(serverMessage);
					} catch (InterruptedException e) {
						mui.addMessage("[ERROR]Interrupted. TERMINATING.");
						sendMessage(ERROR + " " + Server.BOARD
								+ " My client got interrupted.");
						shutdown();
					}
				} else {
					mui.addMessage("[ERROR]Can't make the move on both the local board, and the board on the server. TERMINATING.");
					sendMessage(ERROR
							+ " "
							+ Server.BOARD
							+ " I can't make the specified move on the local board, and the Board you just sent me. TERMINATING.");
					shutdown();
				}
			}
		}
		mui.addMessage(board.toString());
	}

	/**
	 * This method sends a message to the ClientHandler using the OutputStream
	 * out.
	 * 
	 * @param msg
	 *            The message to be sent.
	 */
	//@ requires msg != null;
	public void sendMessage(String msg) {
		try {
			out.write(msg);
			out.newLine();
			out.flush();
		} catch (IOException e) {
			shutdown();
		}
	}

	public Boolean isConnected() {
		return isConnected;
	}

	public boolean isIngame() {
		return board != null;
	}

	/**
	 * This method closes the Socket connection and exits the program. On a side
	 * note, before it does this, it also sets the loop and isIngame variables
	 * for this Client to false.
	 */
	public void shutdown() {
		if (loop) {
			loop = false;
			sendMessage(Client.QUIT + " Shutdown");
			try {
				sock.close();
			} catch (IOException e) {
				e.printStackTrace();
			}
		}
	}

	/**
	 * This method returns the name of this Client.
	 */
	/*@ pure */public String getClientName() {
		return clientName;
	}

	/**
	 * This method makes a Board out of the packet the server sends when the
	 * Board is requested.
	 * 
	 * @param line
	 *            The Boardpacket the Server sent.
	 * @return A new Board object with the Board as sent by the Server.
	 */
	//@ requires line != null;
	public Board toBoard(String line) {
		String[] protocol = line.split(" ");
		Board test = null;
		try {
			int boardColumns = Integer.parseInt(protocol[1]);
			int boardRows = Integer.parseInt(protocol[2]);

			test = new Board(boardRows, boardColumns);
			int i = 3;
			for (int row = boardRows - 1; row >= 0; row--) {
				for (int col = 0; col < boardColumns; col++) {
					if (Integer.parseInt(protocol[i]) == 0) {
						//Disc.EMPTY
						test.setField(row, col, Disc.EMPTY);
					} else if (Integer.parseInt(protocol[i]) == 1) {
						//Disc.YELLOW
						test.setField(row, col, Disc.YELLOW);
					} else if (Integer.parseInt(protocol[i]) == 2) {
						//Disc.RED
						test.setField(row, col, Disc.RED);
					}
					i++;
				}
			}

		} catch (NumberFormatException e) {
			mui.addMessage("[ERROR]Server sent a wrong board. TERMINATING.");
			sendMessage(ERROR + " " + Server.BOARD
					+ " You sent me an invalid Board. TERMINATING.");
			shutdown();
		}
		return test;
	}

	/**
	 * This method is used to convert an Stringarray to a single String.
	 * 
	 * @param array
	 *            The array to convert.
	 * @return The array converted to one line.
	 */
	//@ requires array != null;
	public String arrayToLine(String[] array) {
		String retLine = "";
		for (int i = 1; i < array.length; i++) {
			retLine += " " + array[i];
		}
		return retLine;
	}

	/**
	 * Method to request the board from the server.
	 */
	private void requestBoard() {
		sendMessage(REQUEST_BOARD);
	}

	/**
	 * Method to add an invite to the list of people this Client has invited.
	 * 
	 * @param name
	 *            The name this Client just invited.
	 */
	public void addClientInvite(String name) {
		addClientInvite(name, 7, 6);
	}

	/**
	 * Method to add an invite to the list of people this Client has invited
	 * with a custom Board size.
	 * 
	 * @param name
	 *            The name this Client just invited.
	 * @param BoardX
	 *            The custom Board size's X value.
	 * @param BoardY
	 *            The custom Board size's Y value.
	 */
	public void addClientInvite(String name, int BoardX, int BoardY) {
		invited.put(name, new Integer[] { BoardX, BoardY });
	}

	/**
	 * Method to add an invite to the list of people this Client has been
	 * invited by.
	 * 
	 * @param name
	 *            The name this Client just got invited by.
	 */
	public void addServerInvite(String name) {
		addServerInvite(name, 7, 6);
	}

	/**
	 * Method to add an invite to the list of people this Client has been
	 * invited by with a custom Board size.
	 * 
	 * @param name
	 *            The name this Client just got invited by.
	 * @param BoardX
	 *            The custom Board size's X value.
	 * @param BoardY
	 *            The custom Board size's Y value.
	 */
	public void addServerInvite(String name, int BoardX, int BoardY) {
		invitedBy.put(name, new Integer[] { BoardX, BoardY });
	}

	/**
	 * Method to remove an invite from the list of people this client has
	 * invited. It's called when the server sends a Server.DECLINE_INVITE
	 * packet.
	 * 
	 * @param name
	 *            The name of the person who declined the invite.
	 */
	public void removeServerInvite(String name) {
		invited.remove(name);
	}

	/**
	 * If the server sent a valid Leaderboard, this method adds the formatted
	 * leaderboard to the View.
	 * 
	 * @param serverMessage
	 *            The full message the server sent.
	 */
	public void showLeaderBoard(String[] serverMessage) {
		if ((serverMessage.length - 1) % 5 == 0) {
			int amountOfPlayers = (serverMessage.length - 1) / 5;
			for (int i = 0; i < amountOfPlayers; i++) {
				mui.addMessage(serverMessage[((i * 5) + 5)] + ". "
						+ serverMessage[((i * 5) + 1)] + " Wins: "
						+ serverMessage[((i * 5) + 2)] + " Draws: "
						+ serverMessage[((i * 5) + 3)] + " Losses: "
						+ serverMessage[((i * 5) + 4)]);
			}
		} else {
			mui.addMessage("[ERROR]Didn't get a valid Leaderboard from the Server.");
			sendMessage(ERROR + " " + Server.LEADERBOARD
					+ " Didn't get a valid Leaderboard from your Server :(");
		}
	}

	public void setUpPlayer(String askName) {
		String[] splitName = askName.split("\\s+");
		if (splitName[0].equals("-N")) {
			if (splitName.length == 1) {
				this.clientName = "NaivePlayer";
				this.computerPlayer = new ComputerPlayer(Disc.YELLOW,
						new NaiveStrategy());
			} else {
				this.clientName = splitName[1];
				this.computerPlayer = new ComputerPlayer(Disc.YELLOW,
						new NaiveStrategy());
			}
		} else if (splitName[0].equals("-S")) {
			if (splitName.length == 1) {
				this.clientName = "SmartPlayer";
				this.computerPlayer = new ComputerPlayer(Disc.YELLOW,
						new SmartStrategy());
			} else {
				this.clientName = splitName[1];
				this.computerPlayer = new ComputerPlayer(Disc.YELLOW,
						new SmartStrategy());
			}
		} else {
			this.clientName = splitName[0];
			this.computerPlayer = null;
		}
		isConnected = false;
		sendMessage(CONNECT + " " + getClientName() + " " + CLIENT_FEATURES);
	}

	/**
	 * Sends a Client.QUIT message to the server, and then shuts down the
	 * 
	 */
	public void quit() {
		sendMessage(Client.QUIT + " Disconnected.");
		shutdown();
	}

	/**
	 * Shows the commands that are available. In case the client is in-game,
	 * different commands are shown than when he's not.
	 */
	public void help() {
		if (isIngame()) {
			mui.addMessage("[HELP]Available commands are: MOVE <column>, PING and QUIT");
		} else {
			mui.addMessage("[HELP]Available commands are: INVITE <player>, ACCEPT <player>, DECLINE <player>, CHAT <message>, LOBBY, LEADERBOARD, PING and QUIT");
		}
	}

	/**
	 * Forwards the move the player just made to the server, if the move was
	 * valid, and there was a move requested.
	 * 
	 * @param input
	 *            The raw message the server sent.
	 * @param splitInput
	 *            The message the server sent, split up in an array.
	 */
	public void move(String input, String[] splitInput) {
		//TODO: checken of move requested en humanplayer
		if (moveRequested) {
			moveRequested = false;
			sendMessage(input);
			if (splitInput.length == 2) {
				try {
					Integer.parseInt(splitInput[1]);

				} catch (NumberFormatException | ArrayIndexOutOfBoundsException e) {
					mui.addMessage("[ERROR]Please enter a valid move after MOVE.");
				}
			} else {
				mui.addMessage("[ERROR]Please enter a valid move after MOVE.");
			}
		} else {
			mui.addMessage("[ERROR]There was no move requested.");

		}
	}

	/**
	 * Forwards the invite the player just made to the server, if the player
	 * added a name to invite. It saves the invite in the This method also
	 * supports custom board sizes.
	 * 
	 * @param input
	 *            The raw message the server sent.
	 * @param splitInput
	 *            The message the server sent, split up in an array.
	 */
	public void invite(String input, String[] splitInput) {
		if (splitInput.length == 1) {
			mui.addMessage("[ERROR]Please add a player to invite.");
		} else if (splitInput.length == 2) {
			addClientInvite(splitInput[1]);
			sendMessage(input);
			mui.addMessage("[INVITE]Tried to invite: " + splitInput[1]
					+ " with default board size.");
		} else if (splitInput.length == 3) {
			mui.addMessage("[ERROR]For a custom board size you need to specify both the BoardX and BoardY");
		} else if (splitInput.length >= 4) {
			try {
				addClientInvite(splitInput[1], Integer.parseInt(splitInput[2]),
						Integer.parseInt(splitInput[3]));
				sendMessage(input);
				mui.addMessage("[INVITE]Tried to invite: " + splitInput[1]
						+ " with the specified custom board size.");
			} catch (NumberFormatException e) {
				mui.addMessage("[INVITE]Please specify the BoardX and BoardY as integers. Invite failed.");
			}
		}
	}

	/**
	 * Forwards the rejected invite to the Server, if the player specified whose
	 * invite to decline.
	 * 
	 * @param input
	 *            The raw message the server sent.
	 * @param splitInput
	 *            The message the server sent, split up in an array.
	 */
	public void decline(String input, String[] splitInput) {
		if (splitInput.length > 1) {
			removeServerInvite(splitInput[1]);
			sendMessage(input);
			mui.addMessage("[INVITE]Tried to decline " + splitInput[1]
					+ "'s invite.");
		} else {
			mui.addMessage("[INVITE]Please specify whose invite you'd like to decline.");
		}
	}
}
